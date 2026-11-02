// cdcl.cpp
// Faithful C++ translation of cdcl.py (complete CDCL solver).
// Preserves every trick: two-watched-literal propagation, 1-UIP conflict
// analysis, recursive clause minimization, LBD-based clause-DB reduction,
// Luby restarts, EVSIDS (ratio 1.05) with frequency-based initialization,
// and phase saving. Counters are kept identical to the Python version
// (propagation counted once per literal processed = MiniSat-aligned).
//
// Build:  g++ -std=c++17 -O2 -o cdcl cdcl.cpp
//         (no -lstdc++fs needed: directory listing uses POSIX dirent, which
//          works on any GCC without extra link flags)
// Run:    ./cdcl <benchmark_folder> [output_csv]

#include <iostream>
#include <cstdlib>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include <dirent.h>
#include <unordered_map>
#include <unordered_set>
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cmath>
#include <functional>
#include <limits>

// ------------------------- DIMACS parsing (ports parseFile) ----------------
static int parseFile(const std::string& text, std::vector<std::vector<int>>& clauses) {
    int num_vars = 0;
    std::vector<int> tokens;
    std::istringstream all(text);
    std::string line;
    while (std::getline(all, line)) {
        // strip trailing '\r' and surrounding whitespace
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

// Clause status codes (mirror the ('SAT'|'UNSAT'|'UNIT'|'UNRESOLVED') tuple).
enum { ST_SAT = 0, ST_UNSAT = 1, ST_UNIT = 2, ST_UNRESOLVED = 3 };

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
    std::vector<int> value;      // indexed by var, value[var] in {-1,0,1}
    std::vector<int> level;      // decision level per var
    std::vector<int> reason;     // clause index that forced var, -1 = decision/none
    int num_assigned = 0;
    std::vector<int> trail;
    int decision_level = 0;

    // watched literals
    std::vector<char> active;    // per clause
    std::vector<int> watch1;     // index of 1st watched literal inside clause
    std::vector<int> watch2;     // index of 2nd watched literal inside clause
    std::unordered_map<int, std::vector<int>> watchlist;  // lit -> clause indices

    // clause metadata for LBD reduction
    std::vector<char> clause_is_learned;
    std::vector<double> clause_activity;
    std::vector<int> clause_lbd;
    std::vector<int> learned_clause_indices;
    long long conflict_budget = 0;   // 0 = unlimited; else give up after this many conflicts

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
    long long vsids_num_increments = 0;
    long long vsids_rescale = 1250;
    double vsids_rescale_ratio = 1e100;
    std::vector<double> activity;   // activity[v]
    std::vector<int> phase;         // 0 none, 1 last true, -1 last false

    CDCLSolver(std::vector<std::vector<int>> cls, int num_vars)
        : clauses(std::move(cls)) {
        n = num_vars;

        value.assign(n + 1, -1);
        level.assign(n + 1, 0);
        reason.assign(n + 1, -1);
        trail.reserve(n + 1);

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

        // frequency-based VSIDS initialization (count each var once per clause)
        for (const auto& clause : clauses) {
            std::unordered_set<int> seen_in_clause;
            for (int lit : clause) {
                int v = std::abs(lit);
                if (seen_in_clause.insert(v).second) activity[v] += 1.0;
            }
        }
    }

    inline int litValue(int lit) {
        int v = value[std::abs(lit)];
        if (v < 0) return -1;                 // unassigned
        bool b = (v == 1);
        bool res = (lit > 0) ? b : !b;
        return res ? 1 : 0;
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

    void add_watch(int lit, int ci) { watchlist[lit].push_back(ci); }

    void remove_watch(int lit, int ci) {
        auto it = watchlist.find(lit);
        if (it == watchlist.end()) return;
        auto& vec = it->second;
        for (auto j = vec.begin(); j != vec.end(); ++j) {
            if (*j == ci) { vec.erase(j); return; }
        }
    }

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

    // returns (status, unit_lit). unit_lit valid only when status==ST_UNIT.
    std::pair<int,int> check_clause(const std::vector<int>& clause) {
        std::vector<int> unassigned;
        for (int lit : clause) {
            int v = value[std::abs(lit)];
            if (v < 0) {
                unassigned.push_back(lit);
            } else {
                bool b = (v == 1);
                bool litval = (lit > 0) ? b : !b;
                if (litval) return {ST_SAT, 0};
            }
        }
        if (unassigned.empty()) return {ST_UNSAT, 0};
        if (unassigned.size() == 1) return {ST_UNIT, unassigned[0]};
        return {ST_UNRESOLVED, 0};
    }

    // returns conflicting clause index, or -1 if no conflict.
    int initial_propagate() {
        std::vector<int> queue;
        for (size_t ci = 0; ci < clauses.size(); ++ci) {
            auto st = check_clause(clauses[ci]);
            if (st.first == ST_UNSAT) return (int)ci;
            if (st.first == ST_UNIT) {
                int v = std::abs(st.second);
                if (value[v] == -1) {
                    assign_lit(st.second, (int)ci);
                    queue.push_back(v);
                }
            }
        }
        return propagate(queue);
    }

    // returns conflicting clause index, or -1 if no conflict.
    int propagate(std::vector<int> seeds) {
        std::vector<int> queue = std::move(seeds);
        size_t qi = 0;
        while (qi < queue.size()) {
            int var = queue[qi++];                 // FIFO (matches queue.pop(0))
            int val = value[var];
            if (val < 0) continue;
            num_propagations++;                     // per literal processed
            int false_lit = (val == 1) ? -var : var;

            auto it = watchlist.find(false_lit);
            if (it == watchlist.end()) continue;
            // In-place compaction over the SAME list (MiniSat style): no copy,
            // no O(k) remove_watch. Dead clauses are dropped lazily. Visiting
            // order, assignments, and all counters are identical to the copy
            // version -- only the data-structure bookkeeping changes.
            std::vector<int>& vec = it->second;
            size_t i = 0, j = 0, sz = vec.size();
            while (i < sz) {
                int ci = vec[i];
                if (!active[ci]) { ++i; continue; }   // drop dead clause from list
                auto& clause = clauses[ci];
                int w1 = watch1[ci], w2 = watch2[ci];
                int lit1 = clause[w1], lit2 = clause[w2];
                int other_lit;
                bool updating_watch1;
                if (lit1 == false_lit) { other_lit = lit2; updating_watch1 = true; }
                else if (lit2 == false_lit) { other_lit = lit1; updating_watch1 = false; }
                else { ++i; continue; }               // watch already moved: drop stale ref

                int other_val = litValue(other_lit);
                if (other_val == 1) { vec[j++] = ci; ++i; continue; } // keep watch

                bool moved = false;
                for (int new_idx = 0; new_idx < (int)clause.size(); ++new_idx) {
                    if (new_idx == w1 || new_idx == w2) continue;
                    if (litValue(clause[new_idx]) != 0) {   // not False
                        add_watch(clause[new_idx], ci);     // move to other list
                        if (updating_watch1) watch1[ci] = new_idx;
                        else                 watch2[ci] = new_idx;
                        moved = true;                        // removed from THIS list (skip write)
                        break;
                    }
                }
                if (moved) { ++i; continue; }

                if (other_val == 0) {               // both watches false -> conflict
                    vec[j++] = ci;                   // keep watch (as original did)
                    ++i;
                    while (i < sz) vec[j++] = vec[i++];  // preserve unprocessed tail
                    vec.resize(j);
                    return ci;
                } else {                            // clause is unit -> assign other_lit
                    vec[j++] = ci;                   // keep watch
                    ++i;
                    int unit_var = std::abs(other_lit);
                    if (value[unit_var] == -1) {
                        assign_lit(other_lit, ci);
                        queue.push_back(unit_var);
                    } else {
                        if (litValue(other_lit) == 0) {
                            while (i < sz) vec[j++] = vec[i++];
                            vec.resize(j);
                            return ci;
                        }
                    }
                }
            }
            vec.resize(j);
        }
        return -1;
    }

    void bump_clause_activity(int ci) {
        if (ci < 0) return;
        if (!clause_is_learned[ci]) return;
        clause_activity[ci] += 1.0;
    }

    void bump_vsids(const std::vector<int>& variables) {
        if (vsids_num_increments >= vsids_rescale) {
            vsids_increment /= vsids_rescale_ratio;
            for (int v = 1; v <= n; ++v) activity[v] /= vsids_rescale_ratio;
            vsids_num_increments = 0;
        }
        for (int v : variables) activity[v] += vsids_increment;
        vsids_num_increments++;
        vsids_increment *= vsids_ratio;
    }

    // 1-UIP analysis. conflict_ci = conflicting clause index.
    // Fills out_learned, returns backjump level.
    int analyze_conflict(int conflict_ci, std::vector<int>& out_learned) {
        num_conflicts++;
        bump_clause_activity(conflict_ci);

        int current_level = decision_level;
        std::vector<int> learned;
        std::vector<char> seen(n + 1, 0);
        int path_count = 0;

        // touched vars, preserving first-seen order; dedup via a flag array.
        std::vector<int> touched;
        std::vector<char> touched_flag(n + 1, 0);
        auto touch = [&](int v) {
            if (!touched_flag[v]) { touched_flag[v] = 1; touched.push_back(v); }
        };

        int clause_ci = conflict_ci;       // index of current clause being resolved
        int p = 0;                          // 0 means "None" (var ids start at 1)
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

        // asserting literal (negation of p's current value)
        if (value[p] == 1) learned.push_back(-p);
        else               learned.push_back(p);

        int backjump_level = 0;
        int asserting_var = p;
        for (int lit : learned) {
            int var = std::abs(lit);
            if (var == asserting_var) continue;
            if (level[var] > backjump_level) backjump_level = level[var];
        }

        bump_vsids(touched);
        out_learned = std::move(learned);
        return backjump_level;
    }

    void backtrack(int target_level) {
        while (!trail.empty() && level[trail.back()] > target_level) {
            int var = trail.back();
            trail.pop_back();
            value[var] = -1;        // phase[var] intentionally preserved
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
        if (best_var == 0) return 0;         // none (all assigned)
        if (phase[best_var] == 0) return -best_var;
        return (phase[best_var] > 0) ? best_var : -best_var;
    }

    long long luby(long long i) {
        long long k = 1;
        while (true) {
            if (i == ( (1LL << k) - 1 )) return (1LL << (k - 1));
            else if ( (1LL << (k - 1)) <= i && i < ((1LL << k) - 1) ) {
                i = i - (1LL << (k - 1)) + 1;
                k = 1;
            } else {
                k++;
            }
        }
    }

    int compute_lbd(const std::vector<int>& clause) {
        std::unordered_set<int> levels;
        for (int lit : clause) levels.insert(level[std::abs(lit)]);
        return (int)levels.size();
    }

    int compute_backjump_level(const std::vector<int>& learned) {
        if (learned.empty()) return -1;
        int asserting_var = std::abs(learned.back());
        int bl = 0;
        for (int lit : learned) {
            if (std::abs(lit) != asserting_var)
                if (level[std::abs(lit)] > bl) bl = level[std::abs(lit)];
        }
        return bl;
    }

    // recursive clause minimization (ccmin_mode=2 style), ports minimize_learned_clause
    std::vector<int> minimize_learned_clause(const std::vector<int>& learned) {
        if (learned.size() <= 1) return learned;
        std::unordered_set<int> clause_vars;
        for (int l : learned) clause_vars.insert(std::abs(l));
        std::unordered_map<int, char> cache;   // var -> 0/1 (redundant?)

        // returns whether 'lit' is redundant
        std::function<bool(int)> redundant = [&](int lit) -> bool {
            int var = std::abs(lit);
            int r = reason[var];
            if (r < 0) return false;
            for (int q : clauses[r]) {
                int qv = std::abs(q);
                if (qv == var) continue;
                if (clause_vars.count(qv)) continue;
                if (level[qv] == 0) continue;
                auto it = cache.find(qv);
                if (it != cache.end()) {
                    if (it->second) continue;
                    return false;
                }
                if (reason[qv] >= 0 && redundant(q)) { cache[qv] = 1; continue; }
                cache[qv] = 0;
                return false;
            }
            return true;
        };

        int asserting = learned.back();
        std::vector<int> minimized;
        for (size_t i = 0; i + 1 < learned.size(); ++i) {
            int lit = learned[i];
            if (reason[std::abs(lit)] < 0) minimized.push_back(lit);
            else if (redundant(lit)) { /* drop */ }
            else minimized.push_back(lit);
        }
        minimized.push_back(asserting);     // asserting literal stays LAST
        return minimized;
    }

    // returns index of newly added learned clause
    int add_learned_clause(const std::vector<int>& clause) {
        clauses.push_back(clause);
        int ci = (int)clauses.size() - 1;
        active.push_back(1);
        watch1.push_back(-1);
        watch2.push_back(-1);
        clause_is_learned.push_back(1);
        clause_activity.push_back(1.0);
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
        std::unordered_set<int> locked;
        for (int v = 0; v <= n; ++v) {
            if (reason[v] >= 0) locked.insert(reason[v]);
        }
        std::vector<int> candidates;
        for (int ci : learned_clause_indices) {
            if (!active[ci]) continue;
            if ((int)clauses[ci].size() <= 2) continue;
            if (clause_lbd[ci] <= 2) continue;
            if (locked.count(ci)) continue;
            candidates.push_back(ci);
        }
        if (candidates.size() < 10) return;
        // Python: sort(key=(lbd, -activity), reverse=True), stable.
        // a before b iff lbd[a]>lbd[b], or (==) activity[a]<activity[b].
        std::stable_sort(candidates.begin(), candidates.end(),
            [&](int a, int b) {
                if (clause_lbd[a] != clause_lbd[b]) return clause_lbd[a] > clause_lbd[b];
                return clause_activity[a] < clause_activity[b];
            });
        size_t delete_count = candidates.size() / 2;
        for (size_t i = 0; i < delete_count; ++i) {
            active[candidates[i]] = 0;
            num_deleted_clauses++;
        }
        num_clause_reductions++;
    }

    // Main CDCL loop. returns true = SAT, false = UNSAT.
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

        while (true) {
            if (conflict_budget > 0 && num_conflicts >= conflict_budget) return 2;
            if (conflict != -1) {
                if (decision_level == 0) return false;
                std::vector<int> learned;
                int backtrack_level = analyze_conflict(conflict, learned);
                int old_len = (int)learned.size();
                learned = minimize_learned_clause(learned);
                num_clause_literals_removed += old_len - (int)learned.size();
                backtrack_level = compute_backjump_level(learned);
                int learned_idx = add_learned_clause(learned);

                backtrack(backtrack_level);
                decision_level = backtrack_level;

                auto st = check_clause(clauses[learned_idx]);
                if (st.first == ST_UNSAT) { conflict = learned_idx; continue; }
                std::vector<int> seeds;
                if (st.first == ST_UNIT) {
                    assign_lit(st.second, learned_idx);
                    seeds.push_back(std::abs(st.second));
                }
                conflict = propagate(seeds);
            } else {
                if (num_assigned == n) return true;

                if ((num_conflicts - conflicts_at_last_restart) >= restart_base * luby(luby_index)) {
                    conflicts_at_last_restart = num_conflicts;
                    luby_index += 1;
                    num_restarts += 1;
                    backtrack(0);
                    decision_level = 0;
                    conflict = -1;
                    continue;
                }

                if (num_conflicts >= next_reduce) {
                    reduce_clause_database();
                    next_reduce += reduce_inc;
                }

                int lit = choose_literal_vsids();
                if (lit == 0) return true;
                int var = std::abs(lit);
                decision_level += 1;
                num_decisions += 1;
                assign_lit(lit, -1);
                conflict = propagate(std::vector<int>{var});
            }
        }
    }
};


int main(int argc, char* argv[]) {
    if (argc != 2 && argc != 3) {
        std::cout << "Usage: ./cdcl <benchmark_folder> [output_csv]\n";
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

    // Gather .cnf files via POSIX dirent (portable, no -lstdc++fs dependency).
    std::vector<std::string> files;   // full paths
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
    int sat = 0, unsat = 0, timeouts = 0;
    long long budget = 0;
    { const char* e = std::getenv("CDCL_MAX_CONFLICTS"); if (e) budget = std::atoll(e); }
    double totalTime = 0, minTime = std::numeric_limits<double>::max(), maxTime = 0;

    for (const auto& fp : files) {
        std::string fname = basename(fp);
        std::ifstream in(fp);
        std::stringstream ss; ss << in.rdbuf();
        std::vector<std::vector<int>> clauses;
        int num_vars = parseFile(ss.str(), clauses);

        CDCLSolver solver(std::move(clauses), num_vars);
        solver.conflict_budget = budget;
        std::cerr << "solving " << fname << " ..." << std::endl;
        auto t0 = std::chrono::high_resolution_clock::now();
        int result = solver.solve();
        auto t1 = std::chrono::high_resolution_clock::now();
        double elapsed = std::chrono::duration_cast<std::chrono::microseconds>(t1 - t0).count() / 1e6;

        std::string verdict = (result == 1) ? "SATISFIABLE" : (result == 0) ? "UNSATISFIABLE" : "TIMEOUT";
        if (result == 1) sat++; else if (result == 0) unsat++; else timeouts++;
        totalTime += elapsed;
        minTime = std::min(minTime, elapsed);
        maxTime = std::max(maxTime, elapsed);
        tot_dec += solver.num_decisions; tot_conf += solver.num_conflicts;
        tot_prop += solver.num_propagations; tot_learn += solver.num_learned;
        tot_restart += solver.num_restarts; tot_min += solver.num_clause_literals_removed;
        tot_del += solver.num_deleted_clauses;

        std::cout << fname << "," << verdict << ","
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
    if (writeCSV) std::cout << "\nResults written to " << argv[2] << "\n";
    return 0;
}