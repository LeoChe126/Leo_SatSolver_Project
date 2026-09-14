"""
Steps: 
1. Run WalkSAT first
2. WalkSAT returns the partial best assignment (phase) 
3. Use that assignment to initialize the CDCL phase array 
4. Then use CDCL VSIDS to solve normally and completely
"""


import sys
import time 
import os 
import random
import multiprocessing as mp #For tracking perfile processing time, adding timeouts per file. 

def parseFile(text):
    num_vars = 0
    tokens = []
    for line in text.splitlines():
        line = line.strip()
        if not line or line[0] == 'c' or line[0] == '%': 
            continue
        if line == "0": 
            continue 
        if line[0] == 'p':
            num_vars = int(line.split()[2])
            continue
            
            
        for x in line.split(): 
            tokens.append(int(x))
            
    clauses = [] 
    cur = [] 

    for t in tokens: 
        if t == 0: 
            if cur: 
                clauses.append(cur)
                cur = [] 
        else: 
            cur.append(t)
    
    if cur: 
        clauses.append(cur)
    
    return num_vars, clauses

# Helper functions 

def clause_satisfied_by_assignment(clause, assignment):
    """
    assignment[v] is True/False.
    Index 0 is unused.
    """
    for lit in clause:
        var = abs(lit)
        val = assignment[var]

        if val == (lit > 0):
            return True

    return False


def count_unsatisfied_clauses(clauses, assignment):
    count = 0
    unsat_indices = []

    for i, clause in enumerate(clauses):
        if not clause_satisfied_by_assignment(clause, assignment):
            count += 1
            unsat_indices.append(i)

    return count, unsat_indices

def walksat(clauses, num_vars, max_steps=1000, noise=0.3, seed=None):
    """
    Simple incomplete WalkSAT solver.

    Returns:
        best_assignment, best_unsat_count
    """

    rng = random.Random(seed)

    # Random full assignment
    assignment = [None] + [rng.choice([True, False]) for _ in range(num_vars)]

    best_assignment = assignment[:]
    best_unsat_count, unsat_indices = count_unsatisfied_clauses(clauses, assignment)

    for _ in range(max_steps):
        current_unsat_count, unsat_indices = count_unsatisfied_clauses(clauses, assignment)

        # Found satisfying assignment
        if current_unsat_count == 0:
            return assignment[:], 0

        # Save best assignment seen so far
        if current_unsat_count < best_unsat_count:
            best_unsat_count = current_unsat_count
            best_assignment = assignment[:]

        # Pick one currently unsatisfied clause
        clause_idx = rng.choice(unsat_indices)
        clause = clauses[clause_idx]

        #With probability noise, flip a random variable in the bad clause
        if rng.random() < noise:
            lit = rng.choice(clause)
            flip_var = abs(lit)

        # Otherwise greedily flip the variable that gives fewest unsatisfied clauses
        else:
            best_flip_var = None
            best_flip_unsat = float("inf")

            for lit in clause:
                var = abs(lit)

                # Try flip
                assignment[var] = not assignment[var]
                new_unsat_count, _ = count_unsatisfied_clauses(clauses, assignment)

                # Undo flip
                assignment[var] = not assignment[var]

                if new_unsat_count < best_flip_unsat:
                    best_flip_unsat = new_unsat_count
                    best_flip_var = var

            flip_var = best_flip_var

        # Actually flip selected variable
        assignment[flip_var] = not assignment[flip_var]

    return best_assignment, best_unsat_count

def random_phase_assignment(num_vars, seed=None): 
    # for creating random full assignment for phase initialization.
    # assignment[v] is True/False.
    # Index 0 is unused.
    rng = random.Random(seed)
    return [None] + [rng.choice([True, False]) for _ in range(num_vars)]


class CDCLSolver: 
    def __init__(self, clauses, num_vars=None, initial_phase_assignment=None):
        # clear counters
        self.num_decisions = 0
        self.num_conflicts = 0
        self.num_propagations = 0
        self.num_learned = 0

        self.clauses = clauses

        #implementing two watched variables 
        self.watch1 = [-1] * len(self.clauses)
        self.watch2 = [-1] * len(self.clauses)
        self.watchlist = {}
        self.init_watches()
        """
        Conceptually: 
        self.watch1[i] = index of first watched literal inside clause i
        self.watch2[i] = index of second watched literal inside clause i
        self.watchlist[lit] = list of clause indices currently waching literal lit
        """
        if num_vars is not None:
            self.n = num_vars
        else:
            self.n = max((abs(l) for c in clauses for l in c), default=0)

        self.value = [None] * (self.n + 1) 
        self.level = [0] * (self.n + 1)
        self.reason = [None] * (self.n + 1) # reason, cluase that forced each var( None = decision)
        self.num_assigned = 0
        self.trail = []
        self.decision_level = 0
        self.decisions = []
        self.occ = {}
        self.lit_occ = {}
        for idx, clause in enumerate(self.clauses):
            for lit in clause: 
                self.occ.setdefault(abs(lit), []).append(idx)
                self.lit_occ.setdefault(lit, []).append(idx) 
        
        # VSIDS parameters (following the c++ implementation)
        self.vsids_increment = 0.5 
        self.vsids_ratio = 1.2
        self.vsids_num_increments = 0
        self.vsids_rescale = 1250
        self.vsids_rescale_ratio = 10 ** 100

        self.activity = [0.0] * (self.n + 1) # activity[v] = VSIDS score for v 
        
        self.phase = [0] * (self.n + 1) # stores previous assignment, no saved phase yet (0), last assigned true (1), last assigned false (-1)

        if initial_phase_assignment is not None:
            for v in range(1, self.n + 1): 
                if initial_phase_assignment[v] is True:
                    self.phase[v] = 1
                elif initial_phase_assignment[v] is False:
                    self.phase[v] = -1 

        for clause in self.clauses:
            seen_in_clause = set()
            for lit in clause: 
                v = abs(lit)
                if v not in seen_in_clause: 
                    self.activity[v] += 1.0 
                    seen_in_clause.add(v)


    def assign_lit(self, lit, reason=None):
        var = abs(lit)
        val = lit > 0

        if self.value[var] is not None:
            return

        self.value[var] = val
        self.phase[var] = 1 if val else -1

        self.level[var] = self.decision_level
        self.reason[var] = reason
        self.trail.append(var)
        self.num_assigned += 1
    
    """
    def initial_propagate(self):
        queue = []

        for clause in self.clauses:
            status, unit_lit = self.check_clause(clause)

            if status == 'UNSAT':
                return clause

            if status == 'UNIT':
                v = abs(unit_lit)
                if self.value[v] is None:
                    self.num_propagations += 1
                    #self.assign(v, unit_lit > 0, clause)
                    self.assign_lit(unit_lit, reason=clause)
                    queue.append(v)

        return self.propagate(queue)
    """
    def initial_propagate(self): 
        # initial pass for unit clauses before the main ccl loop, still scans all clauses once
        seeds = []
        changed = True 
        while changed: 
            changed = False 
            for clause in self.clauses: 
                status, unit_lit = self.check_clause(clause) 
                
                if status == 'UNSAT': 
                    return clause 
                
                if status == 'UNIT':
                    var = abs(unit_lit)
                    if self.value[var] is None: 
                        self.num_propagations += 1
                        self.assign_lit(unit_lit, reason=clause) 
                        seeds.append(var)
                        changed = True 
        return self.propagate(seeds)

    def solve(self): 
        self.decision_level = 0
        self.value = [None] * (self.n + 1)
        self.level = [0] * (self.n + 1)
        self.reason = [None] * (self.n + 1) 
        self.num_assigned = 0
        self.trail = []
        self.decisions = []

        conflict = self.initial_propagate()

        while True: 
            if conflict is not None: 
                if self.decision_level == 0: 
                    return False 
                
                backtrack_level, learned = self.analyze_conflict(conflict)
                if backtrack_level < 0:
                    return False
                
                """
                # Add learned clause to the clause database
                self.clauses.append(learned)
                learned_idx = len(self.clauses) - 1
                self.num_learned += 1

                # Update occurrence maps so propagation/heuristics can see the new clause
                for lit in learned:
                    self.occ.setdefault(abs(lit), []).append(learned_idx)
                    self.lit_occ.setdefault(lit, []).append(learned_idx)
                """
                learned_idx = self.add_learned_clause(learned) 


                # Backjump after learning the clause
                self.backtrack(backtrack_level)
                self.decision_level = backtrack_level

                # learned clause is asserting -> exactly one unassigned literal
                status, unit_lit = self.check_clause(learned)

                seeds = []

                if status == 'UNSAT':
                    conflict = learned 
                    continue 

                if status == 'UNIT': 
                    self.num_propagations += 1
                    self.assign_lit(unit_lit, reason=learned)
                    seeds.append(abs(unit_lit))

                conflict = self.propagate(seeds)
            
            else: 
                if self.num_assigned == self.n:
                    return True 
                
                #lit = self.choose_literal()
                lit = self.choose_literal_vsids()

                if lit is None:
                    return True

                var = abs(lit)
                value = lit > 0

                self.decision_level += 1
                self.num_decisions += 1
                # self.assign(var, value, None) # decision --> reason None
                self.assign_lit(lit, reason=None)
                self.decisions.append(var)

                conflict = self.propagate([var])
    
    def propagate(self, seeds): 
        """
        queue = list(seeds)

        while queue: 
            var = queue.pop()
            for idx in self.occ.get(var, []): 
                clause = self.clauses[idx]
                status, unit_lit = self.check_clause(clause)
                if status == 'UNSAT':
                    return clause

                if status == 'UNIT': 
                    v = abs(unit_lit)

                    if self.value[v] is None: 
                        self.num_propagations += 1
                        #self.assign(v, unit_lit > 0, clause) # reason = the unit clause
                        self.assign_lit(unit_lit, reason=clause)
                        queue.append(v)
        
        return None
        """


        # two watched literals propagation
        """
        seeds = variable that were just assigned 
        when a literal becomes true, its negation becomes false 
        inspect clauses watching the false literal. 
        """
        queue = list(seeds) 
        while queue: 
            var = queue.pop(0)
            val = self.value[var]
            if val is None: 
                continue 
        
        # if var = True, then -var is false, vise versa. 
            if val: 
                false_lit = -var
            else: 
                false_lit = var 

            watching = list(self.watchlist.get(false_lit, []))

            for ci in watching: 
                clause = self.clauses[ci]
                w1 = self.watch1[ci]
                w2 = self.watch2[ci]
                lit1 = clause[w1]
                lit2 = clause[w2]
                if lit1 == false_lit: 
                    false_watch_idx = w1
                    other_watch_idx = w2
                    other_lit = lit2 
                    updating_watch1 = True 

                elif lit2 == false_lit: 
                    false_watch = w2 
                    other_watch = w1
                    other_lit = lit1
                    updating_watch1 = False
            
                else: # clause have already moved its watch 
                    continue

                # if the other watch literal is already true, the clause is satisfied, do nothing. 
                other_val = self.lit_value(other_lit)
                if other_val is True:
                    continue 
            
                moved = False 
                for new_idx, new_lit in enumerate(clause): 
                    if new_idx == w1 or new_idx == w2: 
                        continue
                
                    new_val = self.lit_value(new_lit)

                    if new_val is not False: 
                        # move watch from false_lit to new_lit 
                        self.remove_watch(false_lit, ci)
                        self.add_watch(new_lit, ci)

                        if updating_watch1:
                            self.watch1[ci] = new_idx
                        else: 
                            self.watch2[ci] = new_idx
                    
                        moved = True 
                        break 
            
                if moved: 
                    continue
            
                # if could not move watch, clause is either unit or conflict 
                if other_val is False: #both watched lits are flase, clause is conflict 
                    return clause 
            
                else: 
                    #clause is unit, assign other_lit 
                    unit_lit = other_lit
                    unit_var = abs(unit_lit)

                    if self.value[unit_var] is None: 
                        self.num_propagations += 1
                        self.assign_lit(unit_lit, reason=clause)
                        queue.append(unit_var)
                
                    else: 
                        if self.lit_value(unit_lit) is False: 
                            return clause 
        
        return None
            


    
    def check_clause(self, clause):
        unassigned = []
        for lit in clause: 
            v = self.value[abs(lit)] 
            if v is None: 
                unassigned.append(lit) 
            elif v == (lit > 0):
                return ('SAT', None)
            
        if len(unassigned) == 0: 
            return ('UNSAT', None)
        
        if len(unassigned) == 1: 
            return ('UNIT', unassigned[0])
        
        return ('UNRESOLVED', None)
    
    def choose_variable(self): 
        for var in range(1, self.n + 1): 
            if self.value[var] is None: 
                return var 

        return None
    
    def analyze_conflict(self, conflict_clause):
        """
        Perform 1-UIP conflict analysis.

        Input:
            conflict_clause: the clause that is currently falsified.

        Returns:
            backjump_level, learned_clause

        Also:
            bumps VSIDS activity for variables involved in the conflict analysis.
        """ 

        self.num_conflicts += 1

        current_level = self.decision_level

        learned = []
        seen = [False] * (self.n + 1)

        # Number of literals in the current learned clause
        # that are assigned at the current decision level.
        path_count = 0

        # Variables touched during conflict analysis.
        # These are the variables we will bump in VSIDS.
        touched_vars = set()

        clause = conflict_clause
        p = None

        # Start from the most recent assignment on the trail.
        trail_index = len(self.trail) - 1

        while True:
        # Process current conflict/reason clause
            for lit in clause:
                var = abs(lit)

                if var == p:
                    continue

                touched_vars.add(var)

                if not seen[var] and self.level[var] > 0:
                    seen[var] = True

                    if self.level[var] == current_level:
                        path_count += 1
                    else:
                        learned.append(lit)

            # Find the most recent assigned variable from current decision level
            # that appears in the current learned clause.
            while trail_index >= 0:
                candidate = self.trail[trail_index]
                trail_index -= 1

                if seen[candidate]:
                    p = candidate
                    break

            if p is None:
                raise RuntimeError("Conflict analysis failed: no UIP variable found.")

            # We are resolving away p.
            seen[p] = False
            path_count -= 1

            # If path_count is zero, p is the first UIP.
            if path_count == 0:
                break

            reason_clause = self.reason[p]

            if reason_clause is None:
                raise RuntimeError(
                    "Conflict analysis tried to resolve on a decision variable "
                    "before reaching 1-UIP."
                )

            # Next iteration resolves with p's reason clause.
            clause = reason_clause

            for lit in reason_clause:
                touched_vars.add(abs(lit))

        # Add asserting literal.
        # If p was assigned True, learned clause needs -p.
        # If p was assigned False, learned clause needs +p.
        if self.value[p] is True:
            learned.append(-p)
        else:
            learned.append(p)

        # Compute backjump level:
        # highest decision level among all literals except the asserting literal.
        backjump_level = 0
        asserting_var = p

        for lit in learned:
            var = abs(lit)
            if var == asserting_var:
                continue

            backjump_level = max(backjump_level, self.level[var])

        # Bump VSIDS activity for all variables involved in the conflict analysis.
        self.bump_vsids(touched_vars)

        return backjump_level, learned

    # helper function to bump VSIDS scores of variables involved in a conflict
    def bump_vsids(self, variables):
        if self.vsids_num_increments >= self.vsids_rescale:
            self.vsids_increment /= self.vsids_rescale_ratio
            for v in range(1, self.n + 1):
                self.activity[v] /= self.vsids_rescale_ratio
            self.vsids_num_increments = 0

        for v in variables:
            self.activity[v] += self.vsids_increment

        self.vsids_num_increments += 1
        self.vsids_increment *= self.vsids_ratio

    def backtrack(self, target_level):
        while self.trail and self.level[self.trail[-1]] > target_level:
            var = self.trail.pop()

            # value gets cleared
            self.value[var] = None

            # but phase[var] stays saved
            self.level[var] = 0
            self.reason[var] = None
            self.num_assigned -= 1

        self.decision_level = target_level
    
    def num_variabes(self): 
        return self.n

    '''
    def choose_literal(self): 
        best_lit = None
        best_count = -1
        best_pressure = -1.0

        for lit in self.lit_occ: 
            var = abs(lit)
            if self.value[var] is not None: continue 

            count = 0 
            for idx in self.lit_occ.get(lit, []): 
                status, _ = self.check_clause(self.clauses[idx])
                if status != 'SAT': 
                    count += 1
            
            pressure = self.residual_pressure(lit)
            if count > best_count: 
                best_lit = lit
                best_count = count 
                best_pressure = pressure
            
            elif count == best_count and pressure > best_pressure: 
                best_lit = lit
                best_pressure = pressure 
            
            if best_lit is None: 
                return self.choose_variable()
            return best_lit 
    '''

    def choose_literal_vsids(self):
        best_var = None
        best_score = -1.0

        for var in range(1, self.n + 1):
            if self.value[var] is None:
                score = self.activity[var]
                if score > best_score:
                    best_score = score
                    best_var = var

        if best_var is None:
            return None

        # Phase saving:
        # If no saved phase, match the C++ default behavior: choose negative first.
        if self.phase[best_var] == 0:
            return -best_var

        if self.phase[best_var] > 0:
            return best_var
        else:
            return -best_var
    
    def residual_pressure(self, chosen_lit): 
        pressure = 0.0 
        opposite = -chosen_lit
        for idx in self.lit_occ.get(opposite, []):
            clause = self.clauses[idx]
            status, _ = self.check_clause(clause)
            
            if status == 'SAT': 
                continue 
            
            remaining_size = 0 

            for lit in clause: 
                if lit == opposite: 
                    continue 

                val = self.value[abs(lit)]
                if val is None: 
                    remaining_size += 1
                
                elif val == (lit > 0): 
                    remaining_size = None
                    break
                
            if remaining_size is None: 
                continue 
            
            if remaining_size > 0: 
                pressure += 2 ** (-remaining_size)
        
        return pressure
    
    # Additional helper functions (4 below) helping with two watched literals implementation 
    def lit_value(self, lit): 
        # return true if literal is satisfied, false if literal is unsat, None if unassigned. 
        var = abs(lit)
        val = self.value[var]

        if val is None:
            return None

        if lit > 0:
            return val
        else:
            return not val 
    
    def add_watch(self, lit, clause_idx):
        if lit not in self.watchlist: 
            self.watchlist[lit] = []
        self.watchlist[lit].append(clause_idx)
    
    def remove_watch(self, lit, clause_idx):
        # remove clause index from watchlist[lit]
        # 0(length of list), only first implementation (simple version)
        if lit not in self.watchlist: 
            return 
        try: 
            self.watchlist[lit].remove(clause_idx)
        except ValueError: 
            pass 
    
    def init_watches(self):
        #initialize watchesfor all original clauses
        for ci, clause in enumerate(self.clauses): 
            if len(clause) == 0: 
                continue 
            self.watch1[ci] = 0
            self.add_watch(clause[0], ci)

            if len(clause) >= 2: 
                self.watch2[ci] = 1
                self.add_watch(clause[1], ci)
            else: 
                self.watch2[ci] = 0
    
    def add_learned_clause(self, clause):
        #add learned clause and initialize its two watch lits, return the new clause index
        self.clauses.append(clause) 
        ci = len(self.clauses) - 1
        self.watch1.append(-1)
        self.watch2.append(-1) 
        if len(clause) == 0: 
            return ci 
        
        self.watch1[ci] = 0 
        self.add_watch(clause[0], ci)

        if len(clause) >= 2: 
            self.watch2[ci] = 1
            self.add_watch(clause[1], ci)
        else: 
            self.watch2[ci] = 0
        
        self.num_learned += 1
        return ci


#Helper functions to solve a single file and adding timeout per file for large datasat (UF/UUF 250-1065) 
def solve_one_file(args): 
    filepath, mode, file_index = args

    with open(filepath) as f:
        num_vars, clauses = parseFile(f.read())

    initial_assignment = None
    walksat_unsat_count = ""

    if mode == "baseline":
        initial_assignment = None

    elif mode == "random":
        initial_assignment = random_phase_assignment(num_vars, seed=file_index)

    elif mode == "walksat":
        initial_assignment, walksat_unsat_count = walksat(
            clauses,
            num_vars,
            max_steps=1000,
            noise=0.3,
            seed=file_index
        )

    else:
        raise ValueError(f"Unknown mode: {mode}")

    solver = CDCLSolver(
        clauses,
        num_vars,
        initial_phase_assignment=initial_assignment
    )

    start = time.perf_counter()
    result = solver.solve()
    elapsed = time.perf_counter() - start

    verdict = "SATISFIABLE" if result else "UNSATISFIABLE"

    return {
        "file": filepath,
        "mode": mode,
        "time": elapsed,
        "verdict": verdict,
        "decisions": solver.num_decisions,
        "conflicts": solver.num_conflicts,
        "propagations": solver.num_propagations,
        "learned": solver.num_learned,
        "walksat_unsat_count": walksat_unsat_count,
    }

def solve_one_file_with_timeout(filepath, mode, file_index, timeout_seconds):
    with mp.Pool(processes=1) as pool:
        async_result = pool.apply_async(
            solve_one_file,
            ((filepath, mode, file_index),)
        )

        try:
            return async_result.get(timeout=timeout_seconds)

        except mp.TimeoutError:
            pool.terminate()
            pool.join()

            return {
                "file": filepath,
                "mode": mode,
                "time": "",
                "verdict": "TIMEOUT",
                "decisions": "",
                "conflicts": "",
                "propagations": "",
                "learned": "",
                "walksat_unsat_count": "",
            }

if __name__ == "__main__": # LLM implemented this based on my old version

    if len(sys.argv) not in (2, 3, 4, 5):
        print("Usage: python3 cdcl_1uip.py <benchmark_folder> [output_csv] [mode] [timeout_seconds]")
        print("mode options: baseline, random, walksat")
        print("baseline")
        print("random") 
        print("walksat")
        sys.exit(1)

    folder = sys.argv[1]
    output_csv = sys.argv[2] if len(sys.argv) >= 3 else None
    mode = sys.argv[3] if len(sys.argv) >= 4 else "baseline"
    timeout_seconds = int(sys.argv[4]) if len(sys.argv) == 5 else 240 # 4 minutes per file is the timeout
    
    if not os.path.isdir(folder):
        print(f"ERROR: not a folder: {folder}"); sys.exit(1)
    files = sorted(os.path.join(folder, f) for f in os.listdir(folder) if f.endswith(".cnf"))
    if not files:
        print(f"ERROR: no .cnf in {folder}"); sys.exit(1)
    """
    times = []; sat = unsat = 0
    tot_conf = tot_dec = tot_prop = tot_learn = 0
    csv_file = open(output_csv, "w") if output_csv else None
    if csv_file:
        #csv_file.write("file,time,verdict,decisions,conflicts,propagations,learned\n")
        csv_file.write("file,mode,time,verdict,decisions,conflicts,propagations,learned,walksat_unsat\n")
    print(f"Benchmark folder: {folder}\nFound {len(files)} CNF files.\n")
    
    for file_index, filepath in enumerate(files):
        try:
            with open(filepath) as f:
                num_vars, clauses = parseFile(f.read())
            
            initial_assignment = None
            walksat_unsat = ""

            if mode == "baseline":
                initial_assignment = None

            elif mode == "random": 
                initial_assignment = random_phase_assignment(num_vars, seed=0)

            elif mode == "walksat":
                initial_assignment, walksat_unsat_count = walksat(
                    clauses,
                    num_vars,
                    max_steps=1000,
                    noise=0.3,
                    seed=0
                )
                walksat_unsat = walksat_unsat_count

            solver = CDCLSolver(
                clauses,
                num_vars,
                initial_phase_assignment=initial_assignment
            )

            start = time.perf_counter()
            result = solver.solve()
            elapsed = time.perf_counter() - start
            times.append(elapsed)

            if result: 
                verdict = "SATISFIABLE"
            else: 
                verdict = "UNSATISFIABLE"
            
            if result: 
                sat += 1
            else:
                unsat += 1

            tot_conf += solver.num_conflicts
            tot_dec += solver.num_decisions

            tot_prop += solver.num_propagations
            tot_learn += solver.num_learned

            print(f"{filepath},{elapsed:.6f},{verdict}")
            if csv_file:
                csv_file.write(f"{filepath},{mode},{elapsed:.6f},{verdict},"
                                f"{solver.num_decisions},{solver.num_conflicts},"
                                f"{solver.num_propagations},{solver.num_learned}"
                                f",{walksat_unsat}\n")
        except Exception as e:
            print(f"ERROR processing {filepath}: {e}")
            if csv_file: csv_file.write(f"{filepath},,ERROR,,,,\n")
    """
    times = []
    sat = unsat = timeouts = errors = 0
    tot_conf = tot_dec = tot_prop = tot_learn = 0

    csv_file = open(output_csv, "w") if output_csv else None
    if csv_file:
        csv_file.write("file,mode,time,verdict,decisions,conflicts,propagations,learned,walksat_unsat_count\n")

    print(f"Benchmark folder: {folder}")
    print(f"Found {len(files)} CNF files.")
    print(f"Mode: {mode}")
    print(f"Timeout per file: {timeout_seconds}s")
    print()

    for file_index, filepath in enumerate(files):
        try:
            row = solve_one_file_with_timeout(
                filepath,
                mode,
                file_index,
                timeout_seconds
            )

            print(f"{row['file']},{row['time']},{row['verdict']}")

            if csv_file:
                csv_file.write(
                    f"{row['file']},{row['mode']},{row['time']},{row['verdict']},"
                    f"{row['decisions']},{row['conflicts']},"
                    f"{row['propagations']},{row['learned']},"
                    f"{row['walksat_unsat_count']}\n"
                )
                csv_file.flush()

            if row["verdict"] == "TIMEOUT":
                timeouts += 1
                continue

            if row["verdict"] == "SATISFIABLE":
                sat += 1
            elif row["verdict"] == "UNSATISFIABLE":
                unsat += 1
            else:
                errors += 1
                continue

            times.append(row["time"])
            tot_dec += row["decisions"]
            tot_conf += row["conflicts"]
            tot_prop += row["propagations"]
            tot_learn += row["learned"]

        except Exception as e:
            errors += 1
            print(f"ERROR processing {filepath}: {e}")

            if csv_file:
                csv_file.write(f"{filepath},{mode},,ERROR,,,,,\n")
                csv_file.flush()

    if csv_file:
        csv_file.close()

    n = len(times)
    print()

    if n:
        print(f"num solved: {n}")
        print(f"errors/timeouts: {errors + timeouts}")
        print(f"timeouts: {timeouts}")
        print(f"errors: {errors}")
        print(f"min time: {min(times):.6f}")
        print(f"max time: {max(times):.6f}")
        print(f"avg time solved only: {sum(times)/n:.6f}")
        print()
        print(f"avg decisions:    {tot_dec/n:.3f}")
        print(f"avg conflicts:    {tot_conf/n:.3f}")
        print(f"avg propagations: {tot_prop/n:.3f}")
        print(f"avg learned:      {tot_learn/n:.3f}")
    else:
        print("num solved: 0")

    print()
    print(f"SAT count: {sat}")
    print(f"UNSAT count: {unsat}")
    print(f"TIMEOUT count: {timeouts}")
    print(f"ERROR count: {errors}")

    if output_csv:
        print(f"\nResults written to {output_csv}")
    """
    if csv_file: csv_file.close()
    n = len(times)
    print()
    if n:
        print(f"num solved: {n}")
        print(f"min time: {min(times):.6f}")
        print(f"max time: {max(times):.6f}")
        print(f"avg time: {sum(times)/n:.6f}")
        print()
        print(f"avg decisions:    {tot_dec/n:.3f}")
        print(f"avg conflicts:    {tot_conf/n:.3f}")
        print(f"avg propagations: {tot_prop/n:.3f}")
        print(f"avg learned:      {tot_learn/n:.3f}")
        print()
        print(f"SAT count: {sat}")
        print(f"UNSAT count: {unsat}")
    if output_csv:
        print(f"\nResults written to {output_csv}")
    """
    



    


            
