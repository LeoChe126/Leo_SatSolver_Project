// cdcl_v6.cpp -- Stage 6: garbage collection of the clause arena (on top of v5)
//
//   [S6]   When deleted clauses occupy more than 20% of the arena,
//          garbage_collect() copies every live clause into a fresh arena
//          and rewrites all CRefs (watchers, reasons, clause lists).
//          MiniSat-style forwarding: after a clause is copied, its old
//          header is marked RELOCATED and stores the new offset, so each
//          clause is copied exactly once no matter how many places point at
//          it. Live clauses end up compacted in watch-list order.
//          Search is identical to v5; only memory layout changes.
//
// --- Stage 5 changes (from v5) ---
//
//   [S5.1] All clauses live in ONE contiguous std::vector<int32_t> (the
//          "arena"). A clause is referenced by its offset (CRef) and laid
//          out as  [size][flags|lbd][activity(float)][lit0][lit1]...
//          This replaces vector<vector<int>> (one heap block per clause) and
//          the parallel per-clause arrays active/watch1/watch2/
//          clause_is_learned/clause_activity/clause_lbd. Header and literals
//          share a cache line, and clauses learned together sit together.
//   [S5.2] MiniSat watch convention: the two watched literals are always
//          lit[0] and lit[1]. Propagation swaps literals inside the clause
//          instead of storing watch indices, and searches for a replacement
//          watch from lit[2] onward. The implied literal of a reason clause
//          is always lit[0], so "is this clause locked?" is O(1).
//   [S5.3] Deleting a clause only sets a flag and adds its size to
//          `wasted`; the memory is NOT reclaimed in this stage (v6 adds the
//          garbage collector). Watchers of deleted clauses are still purged
//          eagerly at reduction time, as in S1.5.
//   Search note: replacement-watch scan order differs from v4, so conflict
//   counts differ from v4.
//
// --- Stage 4 changes (from v4) ---
//
//   [S4]   The separate prop_queue is gone. The trail already lists every
//          assignment in order, so propagation just walks it with a head
//          index `qhead`: everything in trail[qhead..] is assigned but not
//          yet propagated. backtrack() resets qhead to the new trail end.
//          Same FIFO order as v3, so search is identical; it saves one push
//          per assignment and one buffer.
//
// --- Stage 3 changes (from v3) ---
//
//   [S3]   Each watch-list entry is {clause, blocker}. The blocker is some
//          literal of the clause (initially the other watch). If it is
//          already true the clause is satisfied, so propagation skips it
//          WITHOUT dereferencing the clause -- the common case, and the one
//          that otherwise costs a cache miss per watcher.
//          Note: a satisfied blocker keeps a watch where v2 might have moved
//          it, so watch positions (and hence search) can differ from v2.
//
// --- Stage 2 changes (from v2) ---
//
//   [S2]   Decisions pop the most active unassigned variable from a binary
//          max-heap (MiniSat's VarOrder) instead of scanning all n vars.
//          bump -> sift up; backtrack -> re-insert unassigned vars;
//          decide -> pop until an unassigned var appears (lazy removal).
//          Ties break toward the lower variable index, like v1's scan.
//
// --- Stage 1 changes (from v1) ---
//
//   [S1.1] VSIDS rescale is magnitude-triggered (increment > 1e100), not
//          every 1250 bumps. The old schedule divided by 1e100 while the
//          increment had only grown ~1e26, so activities underflowed to 0.
//   [S1.2] Watch lists are a vector<vector<int>> indexed by literal code
//          (2*v for +v, 2*v+1 for -v) instead of an unordered_map.
//   [S1.3] No per-conflict heap allocations: seen/touched flags, LBD level
//          marks, minimization marks and the propagation queue are reusable
//          members. std::function / unordered_set / unordered_map removed.
//   [S1.4] Clause activity is bumped by a growing cla_inc and decays each
//          conflict (MiniSat style, decay 0.999), with rescale at 1e20.
//   [S1.5] Clause-DB reduction physically frees deleted clauses, removes
//          them from every watch list and from learned_clause_indices.
//   [S1.6] Learned clauses are watched correctly: the asserting literal is
//          moved to position 0 and the highest-level other literal to
//          position 1 before watching. v0 stored the asserting literal LAST
//          but watched positions 0 and 1, i.e. two FALSE literals, so the
//          clause often missed later propagations/conflicts (still sound,
//          because original clauses are watched correctly, but much weaker).
//
// Search behaviour (decisions, restarts, learning, minimization, reduction
// policy) is otherwise unchanged from v0.
//
// Build:  g++ -std=c++17 -O2 -o cdcl_v6 cdcl_v6.cpp
// Run:    ./cdcl_v6 <benchmark_folder> [output_csv]
//         env CDCL_MAX_CONFLICTS=N gives up on an instance after N conflicts

#include <iostream>
#include <cstdlib>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include <dirent.h>
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cmath>
#include <limits>
#include <cstring>

// ------------------------- DIMACS parsing ---------------------------------
static int parseFile(const std::string& text, std::vector<std::vector<int>>& clauses) {
    int num_vars = 0;
    std::vector<int> tokens;
    std::istringstream all(text);
    std::string line;
    while (std::getline(all, line)) {
        size_t a = line.find_first_not_of(" \t\r\n");
        if (a == std::string::npos) continue;
        size_t b = line.find_last_not_of(" \t\r\n");
        line = line.substr(a, b - a + 1);
        if (line.empty()) continue;
        char c0 = line[0];
        if (c0 == 'c' || c0 == '%') continue;
        if (line == "0") continue;
        if (c0 == 'p') {
            std::istringstream iss(line);
            std::string p, cnf;
            iss >> p >> cnf >> num_vars;
            continue;
        }
        std::istringstream iss(line);
        int x;
        while (iss >> x) tokens.push_back(x);
    }
    std::vector<int> cur;
    for (int t : tokens) {
        if (t == 0) {
            if (!cur.empty()) { clauses.push_back(cur); cur.clear(); }
        } else {
            cur.push_back(t);
        }
    }
    if (!cur.empty()) clauses.push_back(cur);
    return num_vars;
}

enum { ST_SAT = 0, ST_UNSAT = 1, ST_UNIT = 2, ST_UNRESOLVED = 3 };

// [S1.2] literal -> dense index for watch lists
static inline int lidx(int lit) { return lit > 0 ? 2 * lit : 2 * (-lit) + 1; }

// [S3] watch-list entry
struct Watcher {
    int ci;        // clause index
    int blocker;   // a literal of the clause; if true, clause is satisfied
};

// [S2] Binary max-heap of variables ordered by activity (MiniSat "Heap").
struct VarHeap {
    std::vector<int> heap;                 // heap[i] = var
    std::vector<int> pos;                  // pos[var] = index in heap, -1 if absent
    const std::vector<double>* act = nullptr;

    void init(int n, const std::vector<double>* a) {
        act = a; heap.clear(); heap.reserve(n); pos.assign(n + 1, -1);
    }
    bool in_heap(int v) const { return pos[v] >= 0; }
    bool empty() const { return heap.empty(); }
    bool better(int a, int b) const {      // a should sit above b
        double x = (*act)[a], y = (*act)[b];
        return x > y || (x == y && a < b);
    }
    void sift_up(int i) {
        int v = heap[i];
        while (i > 0) {
            int parent = (i - 1) >> 1;
            if (!better(v, heap[parent])) break;
            heap[i] = heap[parent]; pos[heap[i]] = i; i = parent;
        }
        heap[i] = v; pos[v] = i;
    }
    void sift_down(int i) {
        int v = heap[i], sz = (int)heap.size();
        while (true) {
            int child = 2 * i + 1;
            if (child >= sz) break;
            if (child + 1 < sz && better(heap[child + 1], heap[child])) child++;
            if (!better(heap[child], v)) break;
            heap[i] = heap[child]; pos[heap[i]] = i; i = child;
        }
        heap[i] = v; pos[v] = i;
    }
    void insert(int v) {
        if (in_heap(v)) return;
        heap.push_back(v); sift_up((int)heap.size() - 1);
    }
    void increased(int v) { if (in_heap(v)) sift_up(pos[v]); }   // activity went up
    int pop_max() {
        int top = heap[0];
        int last = heap.back(); heap.pop_back(); pos[top] = -1;
        if (!heap.empty()) { heap[0] = last; pos[last] = 0; sift_down(0); }
        return top;
    }
};

// [S5.1] Region allocator for clauses. CRef = offset into mem.
typedef int CRef;
static const CRef CREF_UNDEF = -1;

struct ClauseArena {
    // header words
    static const int HDR = 3;              // size, flags|lbd<<4, activity
    static const int F_LEARNED = 1, F_DELETED = 2, F_LOCKED = 4, F_RELOCED = 8;   // [S6]

    std::vector<int32_t> mem;
    size_t wasted = 0;                     // words held by deleted clauses

    CRef alloc(const std::vector<int>& lits, bool learned) {
        CRef cr = (CRef)mem.size();
        mem.push_back((int32_t)lits.size());
        mem.push_back(learned ? F_LEARNED : 0);
        mem.push_back(0);
        mem.insert(mem.end(), lits.begin(), lits.end());
        set_activity(cr, 0.0f);
        return cr;
    }
    int  size(CRef cr) const       { return mem[cr]; }
    int* lits(CRef cr)             { return &mem[cr + HDR]; }
    const int* lits(CRef cr) const { return &mem[cr + HDR]; }
    bool learned(CRef cr) const    { return mem[cr + 1] & F_LEARNED; }
    bool deleted(CRef cr) const    { return mem[cr + 1] & F_DELETED; }
    bool locked_flag(CRef cr) const{ return mem[cr + 1] & F_LOCKED; }
    void set_flag(CRef cr, int f, bool on) { if (on) mem[cr + 1] |= f; else mem[cr + 1] &= ~f; }
    int  lbd(CRef cr) const        { return (int)((uint32_t)mem[cr + 1] >> 4); }
    void set_lbd(CRef cr, int l)   { mem[cr + 1] = (mem[cr + 1] & 15) | (l << 4); }
    float activity(CRef cr) const  { float f; std::memcpy(&f, &mem[cr + 2], 4); return f; }
    void set_activity(CRef cr, float f) { std::memcpy(&mem[cr + 2], &f, 4); }
    void free_clause(CRef cr) {        // [S5.3] mark only, memory stays
        set_flag(cr, F_DELETED, true);
        wasted += HDR + size(cr);
    }
};

struct CDCLSolver {
    // ---- counters ----
    long long num_decisions = 0;
    long long num_conflicts = 0;
    long long num_propagations = 0;
    long long num_learned = 0;
    long long num_clause_literals_removed = 0;
    long long num_restarts = 0;
    long long num_clause_reductions = 0;
    long long num_deleted_clauses = 0;
    long long num_gc = 0;

    int n;
    ClauseArena ca;                            // [S5.1]
    std::vector<CRef> original_crefs;
    std::vector<CRef> learned_crefs;
    bool empty_clause_in_input = false;

    // assignment state. value: -1 unassigned, 0 false, 1 true.
    std::vector<int> value;
    std::vector<int> level;
    std::vector<CRef> reason;                  // CREF_UNDEF = decision/none
    int num_assigned = 0;
    std::vector<int> trail;
    int qhead = 0;                             // [S4]
    int decision_level = 0;

    std::vector<std::vector<Watcher>> watchlist;   // [S1.2][S3]

    long long conflict_budget = 0;

    // [S1.4] clause activity with decay
    double cla_inc = 1.0;
    double cla_decay = 0.999;

    // Luby restarts
    long long restart_base = 100;
    long long luby_index = 1;
    long long conflicts_at_last_restart = 0;

    // clause-DB reduction schedule
    long long reduce_base = 2000;
    long long reduce_inc = 500;
    long long next_reduce = 2000;

    // VSIDS
    double vsids_increment = 0.5;
    double vsids_ratio = 1.05;
    double vsids_rescale_limit = 1e100;        // [S1.1]
    std::vector<double> activity;
    std::vector<int> phase;
    VarHeap order;                             // [S2]

    // [S1.3] reusable scratch buffers
    std::vector<char> seen;
    std::vector<char> touched_flag;
    std::vector<int>  touched;
    std::vector<int>  level_stamp;
    int lbd_stamp = 0;
    std::vector<int>  in_clause_stamp;
    std::vector<int>  cache_stamp;
    std::vector<char> cache_val;
    int min_stamp = 0;

    CDCLSolver(const std::vector<std::vector<int>>& cls, int num_vars) {
        n = num_vars;
        value.assign(n + 1, -1);
        level.assign(n + 1, 0);
        reason.assign(n + 1, CREF_UNDEF);
        trail.reserve(n + 1);
        watchlist.assign(2 * n + 2, {});

        size_t words = 0;
        for (const auto& c : cls) words += ClauseArena::HDR + c.size();
        ca.mem.reserve(words * 4);
        for (const auto& c : cls) {
            if (c.empty()) { empty_clause_in_input = true; continue; }
            CRef cr = ca.alloc(c, false);
            original_crefs.push_back(cr);
            attach(cr);
        }

        activity.assign(n + 1, 0.0);
        phase.assign(n + 1, 0);
        seen.assign(n + 1, 0);
        touched_flag.assign(n + 1, 0);
        level_stamp.assign(n + 2, 0);
        in_clause_stamp.assign(n + 1, 0);
        cache_stamp.assign(n + 1, 0);
        cache_val.assign(n + 1, 0);

        // frequency-based VSIDS initialization (each var once per clause)
        std::vector<int> mark(n + 1, -1);
        for (size_t ci = 0; ci < cls.size(); ++ci)
            for (int lit : cls[ci]) {
                int v = std::abs(lit);
                if (mark[v] != (int)ci) { mark[v] = (int)ci; activity[v] += 1.0; }
            }
        order.init(n, &activity);
        for (int v = 1; v <= n; ++v) order.insert(v);
    }

    inline int litValue(int lit) const {
        int v = value[std::abs(lit)];
        if (v < 0) return -1;
        return ((lit > 0) == (v == 1)) ? 1 : 0;
    }

    void assign_lit(int lit, CRef why) {
        int var = std::abs(lit);
        if (value[var] != -1) return;
        value[var] = (lit > 0) ? 1 : 0;
        phase[var] = (lit > 0) ? 1 : -1;
        level[var] = decision_level;
        reason[var] = why;
        trail.push_back(var);
        num_assigned++;
    }

    // [S5.2] watch lit[0] and lit[1]; blocker = the other watch
    void attach(CRef cr) {
        const int* c = ca.lits(cr);
        if (ca.size(cr) == 1) { watchlist[lidx(c[0])].push_back({cr, c[0]}); return; }
        watchlist[lidx(c[0])].push_back({cr, c[1]});
        watchlist[lidx(c[1])].push_back({cr, c[0]});
    }

    std::pair<int,int> check_clause(CRef cr) const {
        int num_unassigned = 0, last_unassigned = 0;
        const int* c = ca.lits(cr);
        for (int k = 0, sz = ca.size(cr); k < sz; ++k) {
            int lv = litValue(c[k]);
            if (lv == 1) return {ST_SAT, 0};
            if (lv < 0) { num_unassigned++; last_unassigned = c[k]; }
        }
        if (num_unassigned == 0) return {ST_UNSAT, 0};
        if (num_unassigned == 1) return {ST_UNIT, last_unassigned};
        return {ST_UNRESOLVED, 0};
    }

    // Level-0 scan of the input. A unit literal is moved to lit[0] (and the
    // clause re-watched) so that "implied literal is lit[0]" holds for every
    // reason clause.
    CRef initial_propagate() {
        qhead = 0;
        for (CRef cr : original_crefs) {
            auto st = check_clause(cr);
            if (st.first == ST_UNSAT) return cr;
            if (st.first == ST_UNIT && value[std::abs(st.second)] == -1) {
                int* c = ca.lits(cr);
                if (c[0] != st.second) {
                    detach_all(cr);
                    for (int k = 1; k < ca.size(cr); ++k)
                        if (c[k] == st.second) { std::swap(c[0], c[k]); break; }
                    attach(cr);
                }
                assign_lit(st.second, cr);
            }
        }
        return propagate();
    }

    void detach_all(CRef cr) {             // slow path, only used at level 0 setup
        for (auto& wl : watchlist) {
            size_t j = 0;
            for (const Watcher& w : wl) if (w.ci != cr) wl[j++] = w;
            wl.resize(j);
        }
    }

    // [S5.2] MiniSat-style propagation over the packed arena.
    CRef propagate() {
        while (qhead < (int)trail.size()) {
            int var = trail[qhead++];
            num_propagations++;
            int false_lit = (value[var] == 1) ? -var : var;

            std::vector<Watcher>& ws = watchlist[lidx(false_lit)];
            size_t i = 0, j = 0, sz = ws.size();
            while (i < sz) {
                if (litValue(ws[i].blocker) == 1) { ws[j++] = ws[i++]; continue; }   // [S3]
                CRef cr = ws[i].ci;
                int blk = ws[i].blocker;
                int* c = ca.lits(cr);
                int csz = ca.size(cr);
                if (csz == 1) {                            // unit clause falsified
                    while (i < sz) ws[j++] = ws[i++];
                    ws.resize(j);
                    return cr;
                }
                if (c[0] == false_lit) std::swap(c[0], c[1]);   // false lit -> [1]
                ++i;
                int first = c[0];
                Watcher w = {cr, first};
                if (first != blk && litValue(first) == 1) { ws[j++] = w; continue; }

                bool moved = false;
                for (int k = 2; k < csz; ++k) {
                    if (litValue(c[k]) != 0) {             // new watch found
                        c[1] = c[k]; c[k] = false_lit;
                        watchlist[lidx(c[1])].push_back(w);
                        moved = true;
                        break;
                    }
                }
                if (moved) continue;

                ws[j++] = w;                               // clause is unit or conflicting
                if (litValue(first) == 0) {
                    while (i < sz) ws[j++] = ws[i++];
                    ws.resize(j);
                    return cr;
                }
                assign_lit(first, cr);
            }
            ws.resize(j);
        }
        return CREF_UNDEF;
    }

    void bump_clause_activity(CRef cr) {
        if (cr == CREF_UNDEF || !ca.learned(cr)) return;
        float a = ca.activity(cr) + (float)cla_inc;
        ca.set_activity(cr, a);
        if (a > 1e20f) {
            for (CRef lc : learned_crefs) ca.set_activity(lc, ca.activity(lc) * 1e-20f);
            cla_inc *= 1e-20;
        }
    }
    void decay_clause_activity() { cla_inc /= cla_decay; }

    void bump_vsids(const std::vector<int>& variables) {
        for (int v : variables) { activity[v] += vsids_increment; order.increased(v); }
        vsids_increment *= vsids_ratio;
        if (vsids_increment > vsids_rescale_limit) {
            for (int v = 1; v <= n; ++v) activity[v] *= 1e-100;
            vsids_increment *= 1e-100;
        }
    }

    // 1-UIP analysis (same logic as v1..v4)
    int analyze_conflict(CRef conflict, std::vector<int>& learned) {
        num_conflicts++;
        bump_clause_activity(conflict);
        int current_level = decision_level;
        learned.clear();
        touched.clear();
        int path_count = 0;
        auto touch = [&](int v) {
            if (!touched_flag[v]) { touched_flag[v] = 1; touched.push_back(v); }
        };

        CRef cr = conflict;
        int p = 0;
        int trail_index = (int)trail.size() - 1;
        while (true) {
            const int* c = ca.lits(cr);
            for (int k = 0, sz = ca.size(cr); k < sz; ++k) {
                int lit = c[k], var = std::abs(lit);
                if (var == p) continue;
                touch(var);
                if (!seen[var] && level[var] > 0) {
                    seen[var] = 1;
                    if (level[var] == current_level) path_count++;
                    else learned.push_back(lit);
                }
            }
            p = 0;
            while (trail_index >= 0) {
                int candidate = trail[trail_index--];
                if (seen[candidate]) { p = candidate; break; }
            }
            if (p == 0) { std::cerr << "no UIP\n"; std::exit(2); }
            seen[p] = 0;
            path_count--;
            if (path_count == 0) break;
            cr = reason[p];
            if (cr == CREF_UNDEF) { std::cerr << "decision before 1UIP\n"; std::exit(2); }
            bump_clause_activity(cr);
            const int* rc = ca.lits(cr);
            for (int k = 0, sz = ca.size(cr); k < sz; ++k) touch(std::abs(rc[k]));
        }
        learned.push_back(value[p] == 1 ? -p : p);

        int backjump_level = 0;
        for (int lit : learned) {
            int var = std::abs(lit);
            if (var != p && level[var] > backjump_level) backjump_level = level[var];
        }
        bump_vsids(touched);
        for (int v : touched) { touched_flag[v] = 0; seen[v] = 0; }
        decay_clause_activity();
        return backjump_level;
    }

    void backtrack(int target_level) {
        while (!trail.empty() && level[trail.back()] > target_level) {
            int var = trail.back();
            trail.pop_back();
            value[var] = -1;
            level[var] = 0;
            reason[var] = CREF_UNDEF;
            num_assigned--;
            order.insert(var);
        }
        qhead = (int)trail.size();
        decision_level = target_level;
    }

    int choose_literal_vsids() {
        int best_var = 0;
        while (!order.empty()) {
            int v = order.pop_max();
            if (value[v] == -1) { best_var = v; break; }
        }
        if (best_var == 0) return 0;
        if (phase[best_var] == 0) return -best_var;
        return (phase[best_var] > 0) ? best_var : -best_var;
    }

    long long luby(long long i) {
        long long k = 1;
        while (true) {
            if (i == ((1LL << k) - 1)) return (1LL << (k - 1));
            else if ((1LL << (k - 1)) <= i && i < ((1LL << k) - 1)) {
                i = i - (1LL << (k - 1)) + 1;
                k = 1;
            } else {
                k++;
            }
        }
    }

    int compute_lbd(const std::vector<int>& clause) {
        ++lbd_stamp;
        int count = 0;
        for (int lit : clause) {
            int lv = level[std::abs(lit)];
            if (level_stamp[lv] != lbd_stamp) { level_stamp[lv] = lbd_stamp; count++; }
        }
        return count;
    }

    int compute_backjump_level(const std::vector<int>& learned) {
        if (learned.empty()) return -1;
        int asserting_var = std::abs(learned.back());
        int bl = 0;
        for (int lit : learned) {
            int v = std::abs(lit);
            if (v != asserting_var && level[v] > bl) bl = level[v];
        }
        return bl;
    }

    bool redundant(int lit) {
        int var = std::abs(lit);
        CRef r = reason[var];
        if (r == CREF_UNDEF) return false;
        const int* c = ca.lits(r);
        for (int k = 0, sz = ca.size(r); k < sz; ++k) {
            int q = c[k], qv = std::abs(q);
            if (qv == var) continue;
            if (in_clause_stamp[qv] == min_stamp) continue;
            if (level[qv] == 0) continue;
            if (cache_stamp[qv] == min_stamp) {
                if (cache_val[qv]) continue;
                return false;
            }
            if (reason[qv] != CREF_UNDEF && redundant(q)) {
                cache_stamp[qv] = min_stamp; cache_val[qv] = 1; continue;
            }
            cache_stamp[qv] = min_stamp; cache_val[qv] = 0;
            return false;
        }
        return true;
    }

    void minimize_learned_clause(std::vector<int>& learned) {
        if (learned.size() <= 1) return;
        ++min_stamp;
        for (int l : learned) in_clause_stamp[std::abs(l)] = min_stamp;
        int asserting = learned.back();
        size_t j = 0;
        for (size_t i = 0; i + 1 < learned.size(); ++i) {
            int lit = learned[i];
            if (reason[std::abs(lit)] != CREF_UNDEF && redundant(lit)) continue;
            learned[j++] = lit;
        }
        learned[j++] = asserting;
        learned.resize(j);
    }

    // `learned` has the asserting literal last on entry; it is reordered here.
    CRef add_learned_clause(std::vector<int>& learned) {
        // [S1.6] asserting lit at [0], highest-level other at [1]
        if (learned.size() >= 2) {
            std::swap(learned[0], learned.back());
            size_t best = 1;
            for (size_t k = 2; k < learned.size(); ++k)
                if (level[std::abs(learned[k])] > level[std::abs(learned[best])]) best = k;
            std::swap(learned[1], learned[best]);
        }
        CRef cr = ca.alloc(learned, true);
        ca.set_lbd(cr, compute_lbd(learned));
        ca.set_activity(cr, (float)cla_inc);
        learned_crefs.push_back(cr);
        num_learned++;
        attach(cr);
        return cr;
    }

    // [S5.2] a clause is locked iff it is the reason for its lit[0]
    bool locked(CRef cr) const {
        int v = std::abs(ca.lits(cr)[0]);
        return value[v] != -1 && reason[v] == cr;
    }

    void reduce_clause_database() {
        std::vector<CRef> candidates;
        for (CRef cr : learned_crefs) {
            if (ca.size(cr) <= 2) continue;
            if (ca.lbd(cr) <= 2) continue;
            if (locked(cr)) continue;
            candidates.push_back(cr);
        }
        if (candidates.size() < 10) return;
        std::stable_sort(candidates.begin(), candidates.end(),
            [&](CRef a, CRef b) {
                if (ca.lbd(a) != ca.lbd(b)) return ca.lbd(a) > ca.lbd(b);
                return ca.activity(a) < ca.activity(b);
            });
        size_t delete_count = candidates.size() / 2;
        for (size_t i = 0; i < delete_count; ++i) {
            ca.free_clause(candidates[i]);             // [S5.3]
            num_deleted_clauses++;
        }
        for (auto& wl : watchlist) {                   // [S1.5] purge watchers
            size_t j = 0;
            for (const Watcher& w : wl) if (!ca.deleted(w.ci)) wl[j++] = w;
            wl.resize(j);
        }
        size_t j = 0;
        for (CRef cr : learned_crefs) if (!ca.deleted(cr)) learned_crefs[j++] = cr;
        learned_crefs.resize(j);
        num_clause_reductions++;
        maybe_garbage_collect();
    }

    // [S6] compact the arena once >20% of it is garbage
    void maybe_garbage_collect() {
        if (ca.wasted > ca.mem.size() / 5) garbage_collect();
    }

    void garbage_collect() {
        ClauseArena to;
        to.mem.reserve(ca.mem.size() - ca.wasted);
        // Copy a clause once; leave a forwarding pointer in the old header.
        auto reloc = [&](CRef& cr) {
            if (ca.mem[cr + 1] & ClauseArena::F_RELOCED) { cr = ca.mem[cr + 2]; return; }
            CRef nc = (CRef)to.mem.size();
            int words = ClauseArena::HDR + ca.size(cr);
            to.mem.insert(to.mem.end(), ca.mem.begin() + cr, ca.mem.begin() + cr + words);
            ca.mem[cr + 1] |= ClauseArena::F_RELOCED;
            ca.mem[cr + 2] = nc;                       // forwarding address
            cr = nc;
        };
        for (auto& wl : watchlist)                     // watchers (dead ones already purged)
            for (Watcher& w : wl) reloc(w.ci);
        for (int v : trail)                            // reasons (locked => never deleted)
            if (reason[v] != CREF_UNDEF) reloc(reason[v]);
        for (CRef& cr : learned_crefs)  reloc(cr);
        for (CRef& cr : original_crefs) reloc(cr);
        ca.mem.swap(to.mem);
        ca.wasted = 0;
        num_gc++;
    }

    int solve() {   // 1=SAT, 0=UNSAT, 2=UNKNOWN(budget)
        if (empty_clause_in_input) return 0;
        conflicts_at_last_restart = 0;
        luby_index = 1;
        next_reduce = reduce_base;

        CRef conflict = initial_propagate();
        std::vector<int> learned;

        while (true) {
            if (conflict_budget > 0 && num_conflicts >= conflict_budget) return 2;
            if (conflict != CREF_UNDEF) {
                if (decision_level == 0) return 0;
                analyze_conflict(conflict, learned);
                int old_len = (int)learned.size();
                minimize_learned_clause(learned);
                num_clause_literals_removed += old_len - (int)learned.size();
                int backtrack_level = compute_backjump_level(learned);
                CRef cr = add_learned_clause(learned);

                backtrack(backtrack_level);

                auto st = check_clause(cr);
                if (st.first == ST_UNSAT) { conflict = cr; continue; }
                if (st.first == ST_UNIT) assign_lit(st.second, cr);   // st.second == lit[0]
                conflict = propagate();
            } else {
                if (num_assigned == n) return 1;

                if ((num_conflicts - conflicts_at_last_restart) >= restart_base * luby(luby_index)) {
                    conflicts_at_last_restart = num_conflicts;
                    luby_index += 1;
                    num_restarts += 1;
                    backtrack(0);
                    conflict = CREF_UNDEF;
                    continue;
                }

                if (num_conflicts >= next_reduce) {
                    reduce_clause_database();
                    next_reduce += reduce_inc;
                }

                int lit = choose_literal_vsids();
                if (lit == 0) return 1;
                decision_level += 1;
                num_decisions += 1;
                assign_lit(lit, CREF_UNDEF);
                conflict = propagate();
            }
        }
    }

    bool verify(const std::vector<std::vector<int>>& orig) const {
        for (const auto& c : orig) {
            bool sat = false;
            for (int lit : c) if (litValue(lit) == 1) { sat = true; break; }
            if (!sat) return false;
        }
        return true;
    }
};


int main(int argc, char* argv[]) {
    if (argc != 2 && argc != 3) {
        std::cout << "Usage: ./cdcl_v6 <benchmark_folder> [output_csv]\n";
        return 1;
    }
    std::string folder = argv[1];
    bool writeCSV = (argc == 3);
    std::ofstream csv;
    if (writeCSV) {
        csv.open(argv[2]);
        csv << "file,time,verdict,decisions,conflicts,propagations,learned,"
               "restarts,lits_minimized,reductions,deleted_clauses\n";
    }

    std::vector<std::string> files;
    {
        DIR* d = opendir(folder.c_str());
        if (!d) { std::cout << "ERROR: cannot open folder " << folder << "\n"; return 1; }
        struct dirent* ent;
        while ((ent = readdir(d)) != nullptr) {
            std::string name = ent->d_name;
            if (name.size() >= 4 && name.substr(name.size() - 4) == ".cnf")
                files.push_back(folder + "/" + name);
        }
        closedir(d);
    }
    std::sort(files.begin(), files.end());
    if (files.empty()) { std::cout << "ERROR: no .cnf in " << folder << "\n"; return 1; }

    auto basename = [](const std::string& p) {
        size_t s = p.find_last_of('/');
        return (s == std::string::npos) ? p : p.substr(s + 1);
    };

    long long tot_dec = 0, tot_conf = 0, tot_prop = 0, tot_learn = 0;
    long long tot_restart = 0, tot_min = 0, tot_del = 0, tot_gc = 0;
    double tot_arena_mb = 0, max_arena_mb = 0;
    int sat = 0, unsat = 0, timeouts = 0, bad_models = 0;
    long long budget = 0;
    { const char* e = std::getenv("CDCL_MAX_CONFLICTS"); if (e) budget = std::atoll(e); }
    double totalTime = 0, minTime = std::numeric_limits<double>::max(), maxTime = 0;

    for (const auto& fp : files) {
        std::string fname = basename(fp);
        std::ifstream in(fp);
        std::stringstream ss; ss << in.rdbuf();
        std::vector<std::vector<int>> clauses;
        int num_vars = parseFile(ss.str(), clauses);
        std::vector<std::vector<int>> original = clauses;   // for model check

        CDCLSolver solver(std::move(clauses), num_vars);
        solver.conflict_budget = budget;
        auto t0 = std::chrono::high_resolution_clock::now();
        int result = solver.solve();
        auto t1 = std::chrono::high_resolution_clock::now();
        double elapsed = std::chrono::duration_cast<std::chrono::microseconds>(t1 - t0).count() / 1e6;

        std::string verdict = (result == 1) ? "SATISFIABLE" : (result == 0) ? "UNSATISFIABLE" : "TIMEOUT";
        if (result == 1 && !solver.verify(original)) { verdict = "BAD_MODEL"; bad_models++; }
        if (result == 1) sat++; else if (result == 0) unsat++; else timeouts++;
        totalTime += elapsed;
        minTime = std::min(minTime, elapsed);
        maxTime = std::max(maxTime, elapsed);
        tot_dec += solver.num_decisions; tot_conf += solver.num_conflicts;
        tot_prop += solver.num_propagations; tot_learn += solver.num_learned;
        tot_restart += solver.num_restarts; tot_min += solver.num_clause_literals_removed;
        tot_del += solver.num_deleted_clauses;
        tot_gc += solver.num_gc;
        double arena_mb = solver.ca.mem.size() * 4.0 / (1 << 20);
        tot_arena_mb += arena_mb; max_arena_mb = std::max(max_arena_mb, arena_mb);

        std::cout << fname << "," << elapsed << "," << verdict << ","
                  << solver.num_decisions << "," << solver.num_conflicts << ","
                  << solver.num_propagations << "," << solver.num_learned << ","
                  << solver.num_restarts << "," << solver.num_clause_literals_removed << ","
                  << solver.num_clause_reductions << "," << solver.num_deleted_clauses << std::endl;
        if (writeCSV) {
            csv << fname << "," << elapsed << "," << verdict << ","
                << solver.num_decisions << "," << solver.num_conflicts << ","
                << solver.num_propagations << "," << solver.num_learned << ","
                << solver.num_restarts << "," << solver.num_clause_literals_removed << ","
                << solver.num_clause_reductions << "," << solver.num_deleted_clauses << "\n";
            csv.flush();
        }
    }
    if (writeCSV) csv.close();

    int nfiles = (int)files.size();
    std::cout << "\nfiles: " << nfiles << "  solved: " << (nfiles - timeouts) << "  timeouts: " << timeouts << "\n";
    std::cout << "min time: " << minTime << "\n";
    std::cout << "max time: " << maxTime << "\n";
    std::cout << "avg time: " << (totalTime / nfiles) << "\n\n";
    std::cout << "avg decisions:    " << (double)tot_dec / nfiles << "\n";
    std::cout << "avg conflicts:    " << (double)tot_conf / nfiles << "\n";
    std::cout << "avg propagations: " << (double)tot_prop / nfiles << "\n";
    std::cout << "avg learned:      " << (double)tot_learn / nfiles << "\n";
    std::cout << "avg restarts:     " << (double)tot_restart / nfiles << "\n";
    std::cout << "avg lits minimized: " << (double)tot_min / nfiles << "\n";
    std::cout << "avg clauses deleted: " << (double)tot_del / nfiles << "\n";
    std::cout << "avg garbage collections: " << (double)tot_gc / nfiles << "\n";
    std::cout << "arena size at end (MB): avg " << tot_arena_mb / nfiles << ", max " << max_arena_mb << "\n\n";
    std::cout << "SAT count: " << sat << "\n";
    std::cout << "UNSAT count: " << unsat << "\n";
    if (bad_models) std::cout << "BAD MODELS: " << bad_models << "\n";
    if (writeCSV) std::cout << "\nResults written to " << argv[2] << "\n";
    return 0;
}