import sys
import time 
import os 

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


class CDCLSolver: 
    def __init__(self, clauses, num_vars=None):
        # clear counters
        self.num_decisions = 0
        self.num_conflicts = 0
        self.num_propagations = 0
        self.num_learned = 0

        self.clauses = clauses
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
        

    def assign(self, var, val, reason): # added reason argument)
        self.value[var] = val
        self.level[var] = self.decision_level
        self.reason[var] = reason
        self.num_assigned += 1
        self.trail.append(var) 

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
                    self.assign(v, unit_lit > 0, clause)
                    queue.append(v)

        return self.propagate(queue)

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
                self.backtrack(backtrack_level)
                self.decision_level = backtrack_level

                 # learned clause is asserting -> exactly one unassigned literal
                status, unit_lit = self.check_clause(learned)
                if status == 'UNSAT':
                    conflict = learned 
                    continue 
                seeds = [] 
                if status == 'UNIT': 
                    v = abs(unit_lit)
                    self.assign(v, unit_lit > 0, learned) # reason = learend clause
                    seeds = [v]
                conflict = self.propagate(seeds)
            
            else: 
                if self.num_assigned == self.n:
                    return True 
                
                lit = self.choose_literal()
                var = abs(lit)
                value = lit > 0

                self.decision_level += 1
                self.num_decisions += 1
                self.assign(var, value, None) # decision --> reason None
                self.decisions.append(var)

                conflict = self.propagate([var])
    
    def propagate(self, seeds): 
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
                        self.assign(v, unit_lit > 0, clause) # reason = the unit clause
                        queue.append(v)
        
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
    
    ### 1UIP conflict analysis 
    def analyze_conflict(self, conflict):
        self.num_conflicts += 1

        seen = [False] * (self.n + 1)
        learned = []
        counter = 0

        current_level = self.decision_level
        clause = conflict
        p = None
        ti = len(self.trail) - 1

        while True:
            # Add literals from current clause
            for lit in clause:
                v = abs(lit)

                if v == p:
                    continue

                if not seen[v] and self.level[v] > 0:
                    seen[v] = True

                    if self.level[v] == current_level:
                        counter += 1
                    else:
                        learned.append(lit)

            # Find most recent seen variable on the trail
            while ti >= 0 and not seen[self.trail[ti]]:
                ti -= 1

            p = self.trail[ti]
            ti -= 1

            seen[p] = False
            counter -= 1

            # Found first UIP
            if counter == 0:
                break

            # Resolve with reason of p
            clause = self.reason[p]

            if clause is None:
                raise RuntimeError("Tried to resolve on a decision variable before reaching 1-UIP")

        # Add asserting literal
        if self.value[p]:
            learned.append(-p)
            
        else:
            learned.append(p)

        self.num_learned += 1

        # Add learned clause to database
        self.clauses.append(learned)
        idx = len(self.clauses) - 1

        for lit in learned:
            self.occ.setdefault(abs(lit), []).append(idx)
            self.lit_occ.setdefault(lit, []).append(idx)

        # Backjump level = max level among non-asserting literals
        backjump = 0
        for lit in learned:
            v = abs(lit)
            if v != p:
                backjump = max(backjump, self.level[v])

        return backjump, learned
    
    def backtrack(self, level): 

        while self.trail and self.level[self.trail[-1]] > level: 
            var = self.trail.pop()
            self.value[var] = None 
            self.level[var] = 0
            self.reason[var] = None
            self.num_assigned -= 1
        
        while self.decisions and self.value[self.decisions[-1]] is None: 
            self.decisions.pop()
    
    def num_variabes(self): 
        return self.n

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


    
if __name__ == "__main__": # LLM implemented this based on my old version
    if len(sys.argv) not in (2, 3):
        print("Usage: python3 cdcl_1uip.py <benchmark_folder> [output_csv]")
        sys.exit(1)
    folder = sys.argv[1]
    output_csv = sys.argv[2] if len(sys.argv) == 3 else None
    if not os.path.isdir(folder):
        print(f"ERROR: not a folder: {folder}"); sys.exit(1)
    files = sorted(os.path.join(folder, f) for f in os.listdir(folder) if f.endswith(".cnf"))
    if not files:
        print(f"ERROR: no .cnf in {folder}"); sys.exit(1)

    times = []; sat = unsat = 0
    tot_conf = tot_dec = tot_prop = tot_learn = 0
    csv_file = open(output_csv, "w") if output_csv else None
    if csv_file:
        csv_file.write("file,time,verdict,decisions,conflicts,propagations,learned\n")
    print(f"Benchmark folder: {folder}\nFound {len(files)} CNF files.\n")

    for filepath in files:
        try:
            with open(filepath) as f:
                num_vars, clauses = parseFile(f.read())
            solver = CDCLSolver(clauses, num_vars)
            start = time.perf_counter()
            result = solver.solve()
            elapsed = time.perf_counter() - start
            times.append(elapsed)
            verdict = "SATISFIABLE" if result else "UNSATISFIABLE"
            if result: sat += 1
            else: unsat += 1
            tot_conf += solver.num_conflicts; tot_dec += solver.num_decisions
            tot_prop += solver.num_propagations; tot_learn += solver.num_learned
            print(f"{filepath},{elapsed:.6f},{verdict}")
            if csv_file:
                csv_file.write(f"{filepath},{elapsed:.6f},{verdict},"
                                f"{solver.num_decisions},{solver.num_conflicts},"
                                f"{solver.num_propagations},{solver.num_learned}\n")
        except Exception as e:
            print(f"ERROR processing {filepath}: {e}")
            if csv_file: csv_file.write(f"{filepath},,ERROR,,,,\n")

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
        
    



    


            
