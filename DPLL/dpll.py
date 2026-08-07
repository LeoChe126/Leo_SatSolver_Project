#!/usr/bin/env python3
# DPLL SatSolver
 
import sys
import time
import os
 
 
# DIMACS CNF parsing
# A literal is a nonzero int: +v means true, -v means false.
# A clause is a list of literals (a disjunction). A formula is a list of clauses.
 
def parseFile(text): 
    num_vars = 0
    tokens = []
    for line in text.splitlines():
        line = line.strip()

        # skip blank lines, comments, and SATLIB ending markers
        if not line: 
            continue
        if line[0] == 'c':
            continue
        if line[0] == '%':
            continue 

        # some SATLIB files have a trailing 0 after %
        if line == "0":
            continue

        if line[0] == 'p':
            parts = line.split()
            num_vars = int(parts[2])
            continue

        for x in line.split():
            tokens.append(int(x)) 
 
    clauses, cur = [], []
    for t in tokens: # clauses are 0-terminated
        if t == 0:
            clauses.append(cur)
            cur = []
        else:
            cur.append(t)
    if cur: # tolerate a missing final 0
        clauses.append(cur)
    return num_vars, clauses
 
# Core DPLL

def simplify(clauses, lit):

    # Return the formula after asserting lit is true
    # clause containing lit are dropped if satisfied
    # Occrences of negs are false and removed from their clauses

    new = []
    for c in clauses:
        if lit in c:
            continue
        if -lit in c:
            new_clause = [] 
            for x in c: 
                if x != -lit:
                    new_clause.append(x) 
            new.append(new_clause)
        else:
            new.append(c)
    return new
 
 
def dpll(clauses, assignment, stats):
    # Return a satisfying assignment dict {var: bool}, or None if UNSAT.

    #Unit propagation: repeatedly assign forced literals
    while True:
        unit = None
        for c in clauses:
            if len(c) == 0:
                stats["conflicts"] += 1
                return None # empty clause = conflict = UNSAT here
            if len(c) == 1:
                unit = c[0]
                break
        if unit is None:
            break
        
        stats["propagations"] += 1
        assignment[abs(unit)] = (unit > 0)
        clauses = simplify(clauses, unit)
 
    # Pure literal elimination
    counts = {}
    for c in clauses:
        for lit in c:
            counts[lit] = counts.get(lit, 0) + 1
    for lit in list(counts):
        if -lit not in counts: # appears in only one polarity
            assignment[abs(lit)] = (lit > 0) #this checks both positive and negative cases
            clauses = simplify(clauses, lit)
 
    # --- Base cases ---
    if not clauses: # no clauses left -> all satisfied
        return assignment
    for c in clauses: 
        if len(c) == 0: #empty clause -> UNSAT
            stats["conflicts"] += 1
            return None #backtrack and try another assignment 
 
    # Decision: pick a literal and branch 
    lit = clauses[0][0] # pick first literal, could be improved with heuristics!!!!
    stats["decisions"] += 1 # DPLL reached a point where it had to guess.
    for guess in (lit, -lit):
        a = dict(assignment) #copy of current assignment
        a[abs(guess)] = (guess > 0)
        res = dpll(simplify(clauses, guess), a, stats)
        if res is not None: 
            return res
    return None
 
 
# Verification + driver

def verify(clauses, assignment):
    # Independently check that assignment satisfies every original clause.
    for c in clauses:
        clause_satisfied = False
        for l in c:
            if assignment.get(abs(l), False) == (l > 0):
                clause_satisfied = True
                break
        if not clause_satisfied:
            return False
    return True

 
def solve_text(text):
    num_vars, clauses = parseFile(text)
    t0 = time.perf_counter()
    stats = {
        "decisions": 0,
        "conflicts": 0,
        "propagations": 0,
        #"learned_clauses": 0
    }
    result = dpll([c[:] for c in clauses], {}, stats) #first argument makes a copy of all clauses, second argument is empty assignment at first 
    elapsed = time.perf_counter() - t0
 
    if result is None:
        return "UNSAT", None, elapsed, num_vars, len(clauses), stats
 
    # Fill in any free variables so we hand back a complete model.
    for v in range(1, num_vars + 1):
        result.setdefault(v, True)
    assert verify(clauses, result), "BUG: returned a non-satisfying model!"
    return "SAT", result, elapsed, num_vars, len(clauses), stats
 
def main():
    if len(sys.argv) != 2:
        print("Usage:")
        print("  python3 DPLL/dpll.py <cnf_file>")
        print("  python3 DPLL/dpll.py <benchmark_folder>")
        return

    path = sys.argv[1]
    
    # Case 1: user gave one CNF file
    if os.path.isfile(path):
        with open(path) as f:
            verdict, model, elapsed, nv, nc, stats = solve_text(f.read())

        print(f"c file: {path}  ({nv} vars, {nc} clauses)")
        print(f"c time: {elapsed:.4f} s")
        print(f"c decisions: {stats['decisions']}")
        print(f"c conflicts: {stats['conflicts']}")
        print(f"c propagations: {stats['propagations']}")
        print("s " + ("SATISFIABLE" if verdict == "SAT" else "UNSATISFIABLE"))

        if model is not None:
            lits = [str(v if model[v] else -v) for v in sorted(model)]
            print("v " + " ".join(lits) + " 0")

        return

    # Case 2: user gave a benchmark folder
    if os.path.isdir(path):
        files = []

        for filename in os.listdir(path):
            if filename.endswith(".cnf"):
                files.append(os.path.join(path, filename))

        files.sort()

        if not files:
            print(f"No .cnf files found in folder: {path}")
            return

        times = []
        decision_counts = []
        conflict_counts = []
        propagation_counts = []

        sat_count = 0
        unsat_count = 0

        print(f"Benchmark folder: {path}")
        print(f"Found {len(files)} CNF files.")
        print()

        for filepath in files:
            with open(filepath) as f:
                verdict, model, elapsed, nv, nc, stats = solve_text(f.read())

            times.append(elapsed)
            decision_counts.append(stats["decisions"])
            conflict_counts.append(stats["conflicts"])
            propagation_counts.append(stats["propagations"])

            if verdict == "SAT":
                sat_count += 1
                verdict_str = "SATISFIABLE"
            else:
                unsat_count += 1
                verdict_str = "UNSATISFIABLE"

            print(
                f"{filepath},{elapsed},{verdict_str},"
                f"{stats['decisions']},"
                f"{stats['conflicts']},"
                f"{stats['propagations']}"
            )

        print()
        print(f"num solved: {len(files)}")
        print(f"min time: {min(times)}")
        print(f"max time: {max(times)}")
        print(f"avg time: {sum(times) / len(times)}")
        print()
        print(f"avg decisions: {sum(decision_counts) / len(decision_counts)}")
        print(f"avg conflicts: {sum(conflict_counts) / len(conflict_counts)}")
        print(f"avg propagations: {sum(propagation_counts) / len(propagation_counts)}")
        print()
        print(f"SAT count: {sat_count}")
        print(f"UNSAT count: {unsat_count}")

        return

    print(f"ERROR: path does not exist: {path}")
 
 
if __name__ == "__main__":
    main()
