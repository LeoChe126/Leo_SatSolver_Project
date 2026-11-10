// cdcl_v1.cpp -- Stage 1: algorithmic fixes on top of cdcl.cpp (v0)
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
// Build:  g++ -std=c++17 -O2 -o cdcl_v1 cdcl_v1.cpp
// Run:    ./cdcl_v1 <benchmark_folder> [output_csv]
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

    int n;
    std::vector<std::vector<int>> clauses;

    // assignment state. value: -1 unassigned, 0 false, 1 true.
    std::vector<int> value;
    std::vector<int> level;
    std::vector<int> reason;     // clause index, -1 = decision/none
    int num_assigned = 0;
    std::vector<int> trail;
    int decision_level = 0;

    // watched literals
    std::vector<char> active;
    std::vector<int> watch1;
    std::vector<int> watch2;
    std::vector<std::vector<int>> watchlist;   // [S1.2] indexed by lidx(lit)

    // clause metadata for LBD reduction
    std::vector<char> clause_is_learned;
    std::vector<double> clause_activity;
    std::vector<int> clause_lbd;
    std::vector<int> learned_clause_indices;
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

    // [S1.3] reusable scratch buffers
    std::vector<int>  prop_queue;              // propagation FIFO
    std::vector<char> seen;                    // analyze: on implication path
    std::vector<char> touched_flag;            // analyze: var already in touched
    std::vector<int>  touched;                 // analyze: vars to bump
    std::vector<int>  learned_buf;             // analyze: learned clause
    std::vector<int>  level_stamp;             // LBD: level -> stamp
    int lbd_stamp = 0;
    std::vector<int>  in_clause_stamp;         // minimize: var in learned clause
    std::vector<int>  cache_stamp;             // minimize: cache valid for var
    std::vector<char> cache_val;               // minimize: 1 redundant, 0 not
    int min_stamp = 0;
    std::vector<char> locked_buf;              // reduce: clause is a reason

    CDCLSolver(std::vector<std::vector<int>> cls, int num_vars)
        : clauses(std::move(cls)) {
        n = num_vars;

        value.assign(n + 1, -1);
        level.assign(n + 1, 0);
        reason.assign(n + 1, -1);
        trail.reserve(n + 1);
        watchlist.assign(2 * n + 2, {});

        size_t m = clauses.size();
        active.assign(m, 1);
        watch1.assign(m, -1);
        watch2.assign(m, -1);
        init_watches();

        clause_is_learned.assign(m, 0);
        clause_activity.assign(m, 0.0);
        clause_lbd.assign(m, 0);

        next_reduce = reduce_base;

        activity.assign(n + 1, 0.0);
        phase.assign(n + 1, 0);

        seen.assign(n + 1, 0);
        touched_flag.assign(n + 1, 0);
        level_stamp.assign(n + 2, 0);
        in_clause_stamp.assign(n + 1, 0);
        cache_stamp.assign(n + 1, 0);
        cache_val.assign(n + 1, 0);
        prop_queue.reserve(n + 1);

        // frequency-based VSIDS initialization (each var once per clause)
        std::vector<int> mark(n + 1, -1);
        for (size_t ci = 0; ci < clauses.size(); ++ci) {
            for (int lit : clauses[ci]) {
                int v = std::abs(lit);
                if (mark[v] != (int)ci) { mark[v] = (int)ci; activity[v] += 1.0; }
            }
        }
    }

    inline int litValue(int lit) const {
        int v = value[std::abs(lit)];
        if (v < 0) return -1;
        return ((lit > 0) == (v == 1)) ? 1 : 0;
    }

    void assign_lit(int lit, int reason_ci) {
        int var = std::abs(lit);
        if (value[var] != -1) return;
        value[var] = (lit > 0) ? 1 : 0;
        phase[var] = (lit > 0) ? 1 : -1;
        level[var] = decision_level;
        reason[var] = reason_ci;
        trail.push_back(var);
        num_assigned++;
    }

    void add_watch(int lit, int ci) { watchlist[lidx(lit)].push_back(ci); }

    void init_watches() {
        for (size_t ci = 0; ci < clauses.size(); ++ci) {
            auto& clause = clauses[ci];
            if (clause.empty()) continue;
            watch1[ci] = 0;
            add_watch(clause[0], (int)ci);
            if (clause.size() >= 2) {
                watch2[ci] = 1;
                add_watch(clause[1], (int)ci);
            } else {
                watch2[ci] = 0;
            }
        }
    }

    // [S1.3] no temporary vector
    std::pair<int,int> check_clause(const std::vector<int>& clause) const {
        int num_unassigned = 0, last_unassigned = 0;
        for (int lit : clause) {
            int lv = litValue(lit);
            if (lv == 1) return {ST_SAT, 0};
            if (lv < 0) { num_unassigned++; last_unassigned = lit; }
        }
        if (num_unassigned == 0) return {ST_UNSAT, 0};
        if (num_unassigned == 1) return {ST_UNIT, last_unassigned};
        return {ST_UNRESOLVED, 0};
    }

    int initial_propagate() {
        prop_queue.clear();
        for (size_t ci = 0; ci < clauses.size(); ++ci) {
            auto st = check_clause(clauses[ci]);
            if (st.first == ST_UNSAT) return (int)ci;
            if (st.first == ST_UNIT) {
                int v = std::abs(st.second);
                if (value[v] == -1) {
                    assign_lit(st.second, (int)ci);
                    prop_queue.push_back(v);
                }
            }
        }
        return propagate();
    }

    // Propagates everything in prop_queue (caller fills it).
    // returns conflicting clause index, or -1 if no conflict.
    int propagate() {
        std::vector<int>& queue = prop_queue;
        size_t qi = 0;
        while (qi < queue.size()) {
            int var = queue[qi++];
            int val = value[var];
            if (val < 0) continue;
            num_propagations++;
            int false_lit = (val == 1) ? -var : var;

            std::vector<int>& vec = watchlist[lidx(false_lit)];   // [S1.2]
            size_t i = 0, j = 0, sz = vec.size();
            while (i < sz) {
                int ci = vec[i];
                if (!active[ci]) { ++i; continue; }
                auto& clause = clauses[ci];
                int w1 = watch1[ci], w2 = watch2[ci];
                int lit1 = clause[w1], lit2 = clause[w2];
                int other_lit;
                bool updating_watch1;
                if (lit1 == false_lit) { other_lit = lit2; updating_watch1 = true; }
                else if (lit2 == false_lit) { other_lit = lit1; updating_watch1 = false; }
                else { ++i; continue; }

                int other_val = litValue(other_lit);
                if (other_val == 1) { vec[j++] = ci; ++i; continue; }

                bool moved = false;
                for (int new_idx = 0; new_idx < (int)clause.size(); ++new_idx) {
                    if (new_idx == w1 || new_idx == w2) continue;
                    if (litValue(clause[new_idx]) != 0) {
                        add_watch(clause[new_idx], ci);
                        if (updating_watch1) watch1[ci] = new_idx;
                        else                 watch2[ci] = new_idx;
                        moved = true;
                        break;
                    }
                }
                if (moved) { ++i; continue; }

                if (other_val == 0) {
                    vec[j++] = ci; ++i;
                    while (i < sz) vec[j++] = vec[i++];
                    vec.resize(j);
                    return ci;
                } else {
                    vec[j++] = ci; ++i;
                    int unit_var = std::abs(other_lit);
                    if (value[unit_var] == -1) {
                        assign_lit(other_lit, ci);
                        queue.push_back(unit_var);
                    } else if (litValue(other_lit) == 0) {
                        while (i < sz) vec[j++] = vec[i++];
                        vec.resize(j);
                        return ci;
                    }
                }
            }
            vec.resize(j);
        }
        return -1;
    }

    // [S1.4] bump by the (growing) increment, rescale on overflow
    void bump_clause_activity(int ci) {
        if (ci < 0 || !clause_is_learned[ci]) return;
        clause_activity[ci] += cla_inc;
        if (clause_activity[ci] > 1e20) {
            for (int lc : learned_clause_indices) clause_activity[lc] *= 1e-20;
            cla_inc *= 1e-20;
        }
    }
    void decay_clause_activity() { cla_inc /= cla_decay; }

    // [S1.1] rescale only when values get large
    void bump_vsids(const std::vector<int>& variables) {
        for (int v : variables) activity[v] += vsids_increment;
        vsids_increment *= vsids_ratio;
        if (vsids_increment > vsids_rescale_limit) {
            for (int v = 1; v <= n; ++v) activity[v] *= 1e-100;
            vsids_increment *= 1e-100;
        }
    }

    // 1-UIP analysis. Fills out_learned, returns backjump level.
    int analyze_conflict(int conflict_ci, std::vector<int>& out_learned) {
        num_conflicts++;
        bump_clause_activity(conflict_ci);

        int current_level = decision_level;
        std::vector<int>& learned = out_learned;   // [S1.3] caller-owned buffer
        learned.clear();
        touched.clear();
        int path_count = 0;

        auto touch = [&](int v) {
            if (!touched_flag[v]) { touched_flag[v] = 1; touched.push_back(v); }
        };

        int clause_ci = conflict_ci;
        int p = 0;
        int trail_index = (int)trail.size() - 1;

        while (true) {
            const std::vector<int>& clause = clauses[clause_ci];
            for (int lit : clause) {
                int var = std::abs(lit);
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
                int candidate = trail[trail_index];
                trail_index--;
                if (seen[candidate]) { p = candidate; break; }
            }
            if (p == 0) { std::cerr << "no UIP\n"; std::exit(2); }
            seen[p] = 0;
            path_count--;
            if (path_count == 0) break;
            int reason_ci = reason[p];
            if (reason_ci < 0) { std::cerr << "decision before 1UIP\n"; std::exit(2); }
            clause_ci = reason_ci;
            bump_clause_activity(reason_ci);
            for (int lit : clauses[reason_ci]) touch(std::abs(lit));
        }

        if (value[p] == 1) learned.push_back(-p);
        else               learned.push_back(p);

        int backjump_level = 0;
        for (int lit : learned) {
            int var = std::abs(lit);
            if (var == p) continue;
            if (level[var] > backjump_level) backjump_level = level[var];
        }

        bump_vsids(touched);
        // [S1.3] clear scratch flags in O(touched) instead of reallocating
        for (int v : touched) { touched_flag[v] = 0; seen[v] = 0; }
        decay_clause_activity();                   // [S1.4]
        return backjump_level;
    }

    void backtrack(int target_level) {
        while (!trail.empty() && level[trail.back()] > target_level) {
            int var = trail.back();
            trail.pop_back();
            value[var] = -1;
            level[var] = 0;
            reason[var] = -1;
            num_assigned--;
        }
        decision_level = target_level;
    }

    int choose_literal_vsids() {
        int best_var = 0;
        double best_score = -1.0;
        for (int var = 1; var <= n; ++var) {
            if (value[var] == -1) {
                double score = activity[var];
                if (score > best_score) { best_score = score; best_var = var; }
            }
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

    // [S1.3] stamp array instead of unordered_set
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

    // [S1.3] recursive minimization with stamp arrays (same logic as v0)
    bool redundant(int lit) {
        int var = std::abs(lit);
        int r = reason[var];
        if (r < 0) return false;
        for (int q : clauses[r]) {
            int qv = std::abs(q);
            if (qv == var) continue;
            if (in_clause_stamp[qv] == min_stamp) continue;
            if (level[qv] == 0) continue;
            if (cache_stamp[qv] == min_stamp) {
                if (cache_val[qv]) continue;
                return false;
            }
            if (reason[qv] >= 0 && redundant(q)) {
                cache_stamp[qv] = min_stamp; cache_val[qv] = 1; continue;
            }
            cache_stamp[qv] = min_stamp; cache_val[qv] = 0;
            return false;
        }
        return true;
    }

    // Minimizes `learned` in place (asserting literal stays last).
    void minimize_learned_clause(std::vector<int>& learned) {
        if (learned.size() <= 1) return;
        ++min_stamp;
        for (int l : learned) in_clause_stamp[std::abs(l)] = min_stamp;
        int asserting = learned.back();
        size_t j = 0;
        for (size_t i = 0; i + 1 < learned.size(); ++i) {
            int lit = learned[i];
            if (reason[std::abs(lit)] >= 0 && redundant(lit)) continue;  // drop
            learned[j++] = lit;
        }
        learned[j++] = asserting;
        learned.resize(j);
    }

    int add_learned_clause(const std::vector<int>& clause) {
        clauses.push_back(clause);
        int ci = (int)clauses.size() - 1;
        // [S1.6] watch invariant: asserting lit at [0], highest-level other at [1]
        {
            auto& c = clauses[ci];
            if (c.size() >= 2) {
                std::swap(c[0], c.back());
                size_t best = 1;
                for (size_t k = 2; k < c.size(); ++k)
                    if (level[std::abs(c[k])] > level[std::abs(c[best])]) best = k;
                std::swap(c[1], c[best]);
            }
        }
        active.push_back(1);
        watch1.push_back(-1);
        watch2.push_back(-1);
        clause_is_learned.push_back(1);
        clause_activity.push_back(cla_inc);        // [S1.4] counts as one fresh bump
        clause_lbd.push_back(compute_lbd(clause));
        learned_clause_indices.push_back(ci);
        num_learned++;
        if (clauses[ci].empty()) return ci;
        watch1[ci] = 0;
        add_watch(clauses[ci][0], ci);
        if (clauses[ci].size() >= 2) {
            watch2[ci] = 1;
            add_watch(clauses[ci][1], ci);
        } else {
            watch2[ci] = 0;
        }
        return ci;
    }

    void reduce_clause_database() {
        locked_buf.assign(clauses.size(), 0);
        for (int v = 1; v <= n; ++v)
            if (value[v] != -1 && reason[v] >= 0) locked_buf[reason[v]] = 1;

        std::vector<int> candidates;
        for (int ci : learned_clause_indices) {
            if ((int)clauses[ci].size() <= 2) continue;
            if (clause_lbd[ci] <= 2) continue;
            if (locked_buf[ci]) continue;
            candidates.push_back(ci);
        }
        if (candidates.size() < 10) return;
        std::stable_sort(candidates.begin(), candidates.end(),
            [&](int a, int b) {
                if (clause_lbd[a] != clause_lbd[b]) return clause_lbd[a] > clause_lbd[b];
                return clause_activity[a] < clause_activity[b];
            });
        size_t delete_count = candidates.size() / 2;
        for (size_t i = 0; i < delete_count; ++i) {
            int ci = candidates[i];
            active[ci] = 0;
            std::vector<int>().swap(clauses[ci]);  // [S1.5] free the literals
            num_deleted_clauses++;
        }
        // [S1.5] purge dead clauses from every watch list ...
        for (auto& wl : watchlist) {
            size_t j = 0;
            for (int ci : wl) if (active[ci]) wl[j++] = ci;
            wl.resize(j);
        }
        // ... and from the learned-clause index
        size_t j = 0;
        for (int ci : learned_clause_indices) if (active[ci]) learned_clause_indices[j++] = ci;
        learned_clause_indices.resize(j);
        num_clause_reductions++;
    }

    int solve() {   // 1=SAT, 0=UNSAT, 2=UNKNOWN(budget)
        decision_level = 0;
        std::fill(value.begin(), value.end(), -1);
        std::fill(level.begin(), level.end(), 0);
        std::fill(reason.begin(), reason.end(), -1);
        num_assigned = 0;
        trail.clear();
        conflicts_at_last_restart = 0;
        luby_index = 1;
        next_reduce = reduce_base;

        int conflict = initial_propagate();
        std::vector<int> learned;                  // [S1.3] reused every conflict

        while (true) {
            if (conflict_budget > 0 && num_conflicts >= conflict_budget) return 2;
            if (conflict != -1) {
                if (decision_level == 0) return 0;
                analyze_conflict(conflict, learned);
                int old_len = (int)learned.size();
                minimize_learned_clause(learned);
                num_clause_literals_removed += old_len - (int)learned.size();
                int backtrack_level = compute_backjump_level(learned);
                int learned_idx = add_learned_clause(learned);

                backtrack(backtrack_level);

                auto st = check_clause(clauses[learned_idx]);
                if (st.first == ST_UNSAT) { conflict = learned_idx; continue; }
                prop_queue.clear();
                if (st.first == ST_UNIT) {
                    assign_lit(st.second, learned_idx);
                    prop_queue.push_back(std::abs(st.second));
                }
                conflict = propagate();
            } else {
                if (num_assigned == n) return 1;

                if ((num_conflicts - conflicts_at_last_restart) >= restart_base * luby(luby_index)) {
                    conflicts_at_last_restart = num_conflicts;
                    luby_index += 1;
                    num_restarts += 1;
                    backtrack(0);
                    conflict = -1;
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
                assign_lit(lit, -1);
                prop_queue.clear();
                prop_queue.push_back(std::abs(lit));
                conflict = propagate();
            }
        }
    }

    // true iff the current assignment satisfies every clause in `orig`
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
        std::cout << "Usage: ./cdcl_v1 <benchmark_folder> [output_csv]\n";
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
    long long tot_restart = 0, tot_min = 0, tot_del = 0;
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
    std::cout << "avg clauses deleted: " << (double)tot_del / nfiles << "\n\n";
    std::cout << "SAT count: " << sat << "\n";
    std::cout << "UNSAT count: " << unsat << "\n";
    if (bad_models) std::cout << "BAD MODELS: " << bad_models << "\n";
    if (writeCSV) std::cout << "\nResults written to " << argv[2] << "\n";
    return 0;
}
