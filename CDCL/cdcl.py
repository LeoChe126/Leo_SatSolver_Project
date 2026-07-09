import sys
import time
import signal
import os

def parseFile(text):
    num_vars = 0
    tokens = []

    for line in text.splitlines():
        line = line.strip()

        # Skip blank lines, comments, and SATLIB ending markers
        if not line:
            continue

        if line[0] == 'c':
            continue

        if line[0] == '%':
            continue

        # Some SATLIB files have a trailing 0 after %
        if line == "0":
            continue

        # DIMACS header
        if line[0] == 'p':
            parts = line.split()
            num_vars = int(parts[2])
            continue

        for x in line.split():
            tokens.append(int(x))

    clauses = []
    cur = []

    for t in tokens:
        if t == 0:
            clauses.append(cur)
            cur = []
        else:
            cur.append(t)

    # Tolerate missing final 0
    if cur:
        clauses.append(cur)

    return num_vars, clauses

class CDCLSolver:
    def __init__(self, clauses):

        self.clauses = clauses
        self.assignment = {}  # variable -> True/False
        self.decision_level = 0
        self.implication_graph = []
        self.assignment_level = {} # for backtracking, maps variable to decision level
        self.decisions = []
        self.occ = {} # list of occurrences of each variable in clauses, for heuristic branching
        for idx, clause in enumerate(self.clauses): 
            for lit in clause: 
                self.occ.setdefault(abs(lit), []).append(idx) # store index of clause in which variable occurs
        
        self.clause_true_count = [0] * len(self.clauses) # count of true literals in each clause

        # helper functions
    
    def _on_assign(self, var, value): 
        for idx in self.occ.get(var, []): 
            for lit in self.clauses[idx]:
                if abs(lit) == var: 
                    if (lit > 0) == value: 
                        self.clause_true_count[idx] += 1

    def _on_unassign(self, var, value):
        for idx in self.occ.get(var, []):
            for lit in self.clauses[idx]:
                if abs(lit) == var: 
                    if (lit > 0) == value: 
                        self.clause_true_count[idx] -= 1


    def solve(self):
        """
        Main CDCL solving algorithm.
        
        Returns True if satisfiable, False otherwise
        """
        # resets solver state for new solve attempt
        self.decision_level = 0
        self.assignment = {}  
        self.assignment_level = {}  
        self.decisions = []
        
        while True:
            conflict = self.propagate()
            
            if conflict is None:
                # No conflict, check if all variables assigned
                if len(self.assignment) == self.num_variables():
                    return True 
                
                # Choose next variable to branch on
                var = self.choose_variable()
                self.decision_level += 1
                self.assignment[var] = True
                self.assignment_level[var] = self.decision_level
                self.decisions.append(var)

            else:
                #  Conflict detected
                if self.decision_level == 0:
                    return False
                
                # Analyze conflict and backtrack
                backtrack_level = self.analyze_conflict(conflict)
                self.backtrack(backtrack_level)
                self.decision_level = backtrack_level
    
    def propagate(self):
        
        # Unit propagation with BCP (Boolean Constraint Propagation)
        changed = True
        while changed: # keep propagating as long as last iteration assigned a new variable (at least 1)
            changed = False
            for clause in self.clauses:
                status, unit_lit = self.check_clause(clause)
                
                if status == 'UNSAT':
                    return clause
                
                if status == 'UNIT': #exactly 1 unassigned literal
                    var = abs(unit_lit)
                    value = unit_lit > 0 #TRUE
                    if var not in self.assignment:
                        self.assignment[var] = value
                        self.assignment_level[var] = self.decision_level
                        changed = True

        return None # no conflict found 
    
    def check_clause(self, clause):
        # Check clause status: True, False, or None (unresolved)
        # Returns ('SAT', None) | ('CONFLICT', None) | ('UNIT', lit) | ('UNRESOLVED', None).
        # report four distinct states, and only assign on genuine units
        unassigned = []
        
        for lit in clause:
            var = abs(lit)
            if var in self.assignment:
                if self.assignment[var] == (lit > 0):
                    return ('SAT', None) # one true literal satisfies the clause
                
            else:
                unassigned.append(lit)
        
        if len(unassigned) == 0:
            return ('UNSAT', None)
        
        if len(unassigned) == 1:
            return ('UNIT', unassigned[0])
        else: 
            return ('UNRESOLVED', None)
    
    # no longer needed since propagate finds unassigned literals. 
    """
    def get_unassigned_literal(self, clause):
        # Get unassigned literal in clause
        for lit in clause:
            if abs(lit) not in self.assignment:
                return lit
        return None
    """


    
    def choose_variable(self):
        # Choose next variable to branch on
        # Naive branching logic: pick the first unassigned variable
        
        '''
        for var in range(1, self.num_variables() + 1):
            if var not in self.assignment:
                return var
        return None
        '''
        best_var, best_score = None, -1
        for var in range(1, self.num_variables() + 1):
            if var in self.assignment: 
                continue
            score = sum(1 for idx in self.occ.get(var, []) if self.clause_true_count[idx] == 0)
            if score > best_score:
                best_var, best_score = var, score
        return best_var

    def analyze_conflict(self, conflict):
        # Analyze conflict and determine backtrack level
        # Simplified: backtrack to decision_level - 1
        '''
        learned = [] 
        for d in self.decisions: 
            if self.assignment[d]: 
                learned.append(-d)
            else: 
                learned.append(d)
        self.clauses.append(learned)
        return max(0, self.decision_level - 1)
        '''
        # LEARN (trivial version: negation of all current decisions)
        learned = []
        for d in self.decisions:
            if self.assignment[d]: 
                learned.append(-d)
            else: 
                learned.append(d)
        self.clauses.append(learned)
        idx = len(self.clauses) - 1
        self.clause_true_count.append(0) # initialize count for new learned clause
        for lit in learned: 
            v = abs(lit)
            self.occ.setdefault(v, []).append(idx)
            if v in self.assignment and (lit > 0) == self.assignment[v]:
                self.clause_true_count[idx] += 1


        # BACKJUMP: second-highest decision level IN THE LEARNED CLAUSE
        levels = set()
        for lit in learned:
            var = abs(lit)
            if var in self.assignment_level:
                levels.add(self.assignment_level[var])
        levels = sorted(levels)
        if len(levels) <= 1:
            return 0
        return levels[-2]
    
    def backtrack(self, level):
        # Backtrack to given decision level
        vars_to_remove = []
        for var in self.assignment: 
            if self.assignment_level[var] > level:
                vars_to_remove.append(var)
        
        for var in vars_to_remove: 
            self._on_unassign(var, self.assignment[var]) # update clause_true_count
            del self.assignment[var]
            del self.assignment_level[var]
        
        remaining_decisions = []
        for var in self.decisions: 
            if var in self.assignment: 
                remaining_decisions.append(var)
        
        self.decisions = remaining_decisions
    
    def num_variables(self):
        # Get number of variables
        max_var = 0
        for clause in self.clauses:
            for lit in clause:
                max_var = max(max_var, abs(lit))
        return max_var


# same as DPLL 
if __name__ == "__main__":
    if len(sys.argv) not in (2, 3):
        print("Usage: python3 cdcl.py <benchmark_folder> [output_csv]")
        print("Example: python3 CDCL/cdcl.py benchmarks/uf50-218")
        print("Example: python3 CDCL/cdcl.py benchmarks/uuf50-218 cdcl_uuf50_1000.csv")
        sys.exit(1)

    benchmark_folder = sys.argv[1]

    output_csv = sys.argv[2] if len(sys.argv) == 3 else None

    if not os.path.isdir(benchmark_folder):
        print(f"ERROR: Benchmark folder does not exist: {benchmark_folder}")
        sys.exit(1)

    files = []
    for filename in os.listdir(benchmark_folder):
        if filename.endswith(".cnf"):
            full_path = os.path.join(benchmark_folder, filename)
            files.append(full_path)

    files.sort()

    if not files:
        print(f"ERROR: No .cnf files found in {benchmark_folder}")
        sys.exit(1)
    times = []
    sat_count = 0
    unsat_count = 0
    solved_count = 0
    csv_file = None
    if output_csv is not None:
        csv_file = open(output_csv, "w")
        csv_file.write("file,time,verdict\n")

    print(f"Benchmark folder: {benchmark_folder}")
    print(f"Found {len(files)} CNF files.")
    print()

    for filepath in files:
        try:
            with open(filepath, "r") as f:
                text = f.read()

            num_vars, clauses = parseFile(text)

            solver = CDCLSolver(clauses)

            start = time.perf_counter()
            result = solver.solve()
            elapsed = time.perf_counter() - start

            times.append(elapsed)
            solved_count += 1

            if result:
                verdict = "SATISFIABLE"
                sat_count += 1
            else:
                verdict = "UNSATISFIABLE"
                unsat_count += 1

            print(f"{filepath},{elapsed},{verdict}")

            if csv_file is not None:
                csv_file.write(
                    f"{filepath},{elapsed},{verdict}\n"
                )

        except Exception as e:
            print(f"ERROR processing {filepath}: {e}")

            if csv_file is not None:
                csv_file.write(
                    f"{filepath},,ERROR\n"
                )

    if csv_file is not None:
        csv_file.close()

    print()

    if times:
        min_time = min(times)
        max_time = max(times)
        avg_time = sum(times) / len(times)

        print(f"num solved: {solved_count}")
        print(f"min time: {min_time}")
        print(f"max time: {max_time}")
        print(f"avg time: {avg_time}")

        print()
        print(f"SAT count: {sat_count}")
        print(f"UNSAT count: {unsat_count}")

    else:
        print("No benchmark instances were solved.")

    if output_csv is not None:
        print(f"Results written to {output_csv}")
   
