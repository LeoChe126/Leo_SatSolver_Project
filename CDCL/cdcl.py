import sys
import time
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
    def __init__(self, clauses, num_vars=None):
        self.clauses = clauses

        # Change 1: cache variable count
        if num_vars is not None:
            self.n = num_vars
        else:
            max_var = 0
            for clause in clauses:
                for lit in clause:
                    var = abs(lit)
                    if var > max_var:
                        max_var = var
            self.n = max_var   

        # Change 2: flat lists instead of dicts
        self.value = [None] * (self.n + 1)   # None = unassigned
        self.level = [0] * (self.n + 1)      # decision level of each assignment
        self.num_assigned = 0

        # Change 3: assignment trail for fast backtracking
        self.trail = []

        self.decision_level = 0
        self.decisions = []

        # Change 4: occurrence map (var -> clause indices) 
        self.occ = {}
        self.lit_occ = {} # list of literal occurences count for smart heuristics
        for idx, clause in enumerate(self.clauses):
            for lit in clause:
                self.occ.setdefault(abs(lit), []).append(idx)
                self.lit_occ.setdefault(lit, []).append(idx)

    def assign(self, var, val):
        # Single place where assignment bookkeeping happens
        self.value[var] = val
        self.level[var] = self.decision_level
        self.num_assigned += 1
        self.trail.append(var)

    def solve(self):
        """
        Main CDCL solving algorithm.

        Returns True if satisfiable, False otherwise
        """
        # Reset solver state for new solve attempt
        self.decision_level = 0
        self.value = [None] * (self.n + 1)
        self.level = [0] * (self.n + 1)
        self.num_assigned = 0
        self.trail = []
        self.decisions = []

        # One full scan to catch original unit clauses, then queue-driven
        conflict = self.initial_propagate()

        while True:
            if conflict is not None:
                # Conflict detected
                if self.decision_level == 0:
                    return False

                backtrack_level, learned = self.analyze_conflict(conflict)
                self.backtrack(backtrack_level)
                self.decision_level = backtrack_level

                # The learned clause is unit after backtracking:
                # assign its literal and propagate from there.
                status, unit_lit = self.check_clause(learned)
                if status == 'UNSAT':
                    conflict = learned
                    continue
                seeds = []
                if status == 'UNIT':
                    v = abs(unit_lit)
                    self.assign(v, unit_lit > 0)
                    seeds = [v]
                conflict = self.propagate(seeds)

            else:
                # No conflict, check if all variables assigned
                if self.num_assigned == self.n:
                    return True

                # Choose next variable to branch on
                '''
                var = self.choose_variable()
                self.decision_level += 1
                self.assign(var, True)
                self.decisions.append(var)
                conflict = self.propagate([var])
                '''
                lit = self.choose_literal()

                var = abs(lit)
                value = lit > 0

                self.decision_level += 1
                self.assign(var, value)
                self.decisions.append(var)

                conflict = self.propagate([var])

    def initial_propagate(self):
        # Full scan once, to find unit/empty clauses in the original formula
        queue = []
        for clause in self.clauses:
            status, unit_lit = self.check_clause(clause)
            if status == 'UNSAT':
                return clause
            if status == 'UNIT':
                v = abs(unit_lit)
                if self.value[v] is None:
                    self.assign(v, unit_lit > 0)
                    queue.append(v)
        return self.propagate(queue)

    def propagate(self, seeds):
        # Queue-driven unit propagation, only look at clauses containing variables that were just assigned.
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
                        self.assign(v, unit_lit > 0)
                        queue.append(v)

        return None  # no conflict found

    def check_clause(self, clause):
        # Check clause status.
        # Returns ('SAT', None) | ('UNSAT', None) | ('UNIT', lit) | ('UNRESOLVED', None)
        unassigned = []

        for lit in clause:
            v = self.value[abs(lit)]
            if v is None:
                unassigned.append(lit)
            elif v == (lit > 0):
                return ('SAT', None)  # one true literal satisfies the clause

        if len(unassigned) == 0:
            return ('UNSAT', None)

        if len(unassigned) == 1:
            return ('UNIT', unassigned[0])

        return ('UNRESOLVED', None)

    def choose_variable(self):
        # Naive branching: pick the first unassigned variable
        for var in range(1, self.n + 1):
            if self.value[var] is None:
                return var
        return None

    def analyze_conflict(self, conflict):
        # LEARN (trivial version: negation of all current decisions)
        learned = []
        for d in self.decisions:
            if self.value[d]:
                learned.append(-d)
            else:
                learned.append(d)
        self.clauses.append(learned)

        # Register the learned clause in the occurrence map
        idx = len(self.clauses) - 1
        for lit in learned:
            self.occ.setdefault(abs(lit), []).append(idx)
            self.lit_occ.setdefault(lit, []).append(idx) # important for smart heuristics, otherwise it will ignore the learned clause

        # backjump: second-highest decision level in the learned clause
        levels = set()
        for lit in learned:
            var = abs(lit)
            if self.value[var] is not None:
                levels.add(self.level[var])
        levels = sorted(levels)
        if len(levels) <= 1:
            return 0, learned
        return levels[-2], learned

    def backtrack(self, level):
        # Assignments happen in level order, so everything above `level` is a suffix of the trail: just pop it off.
        while self.trail and self.level[self.trail[-1]] > level:
            var = self.trail.pop()
            self.value[var] = None
            self.level[var] = 0
            self.num_assigned -= 1

        # Same suffix property holds for decisions
        while self.decisions and self.value[self.decisions[-1]] is None:
            self.decisions.pop()

    def num_variables(self):
        return self.n

    def choose_literal(self):
        best_lit = None
        best_count = -1
        best_pressure = -1.0

        for lit in self.lit_occ:
            var = abs(lit)

            # Only branch on unassigned variables
            if self.value[var] is not None:
                continue

            # DLIS score: how many unresolved clauses contain this signed literal?
            count = 0

            for idx in self.lit_occ.get(lit, []):
                clause = self.clauses[idx]
                status, _ = self.check_clause(clause)

                if status != 'SAT':
                    count += 1

            # Tie-breaker: opposite-polarity residual pressure
            pressure = self.residual_pressure(lit)

            if count > best_count:
                best_lit = lit
                best_count = count
                best_pressure = pressure

            elif count == best_count:
                if pressure > best_pressure:
                    best_lit = lit
                    best_pressure = pressure
            
        if best_lit is None:
            var = self.choose_variable()
            return var

        return best_lit

    def residual_pressure(self, chosen_lit):
        pressure = 0.0
        opposite = -chosen_lit

        for idx in self.lit_occ.get(opposite, []):
            clause = self.clauses[idx]

            # Skip clauses already satisfied by the current assignment
            status, _ = self.check_clause(clause)

            if status == 'SAT':
                continue

            remaining_size = 0

            for lit in clause:
                if lit == opposite:
                    continue

                var = abs(lit)
                val = self.value[var]

                if val is None:
                    remaining_size += 1
                elif val == (lit > 0):
                    # Clause is already satisfied; ignore it
                    remaining_size = None
                    break

            if remaining_size is None:
                continue

            # If choosing chosen_lit makes the opposite clause shorter,
            # shorter residual clauses get higher pressure.
            if remaining_size > 0:
                pressure += 2 ** (-remaining_size)

        return pressure


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

            solver = CDCLSolver(clauses, num_vars)

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