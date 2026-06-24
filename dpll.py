#!/usr/bin/env python3
# DPLL SatSolver
 
import sys
import time
 
 
# DIMACS CNF parsing
# A literal is a nonzero int: +v means true, -v means false.
# A clause is a list of literals (a disjunction). A formula is a list of clauses.
 
def parse_dimacs(text): 
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
 
 
def dpll(clauses, assignment):
    # Return a satisfying assignment dict {var: bool}, or None if UNSAT.

    #Unit propagation: repeatedly assign forced literals
    while True:
        unit = None
        for c in clauses:
            if len(c) == 0:
                return None # empty clause = conflict = UNSAT here
            if len(c) == 1:
                unit = c[0]
                break
        if unit is None:
            break
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
            return None #backtrack and try another assignment 
 
    # Decision: pick a literal and branch 
    lit = clauses[0][0] # pick first literal, could be improved with heuristics!!!!
    for guess in (lit, -lit):
        a = dict(assignment) #copy of current assignment
        a[abs(guess)] = (guess > 0)
        res = dpll(simplify(clauses, guess), a)
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
    num_vars, clauses = parse_dimacs(text)
    t0 = time.perf_counter()
    result = dpll([c[:] for c in clauses], {}) #first argument makes a copy of all clauses, second argument is empty assignment at first 
    elapsed = time.perf_counter() - t0
 
    if result is None:
        return "UNSAT", None, elapsed, num_vars, len(clauses)
 
    # Fill in any free variables so we hand back a complete model.
    for v in range(1, num_vars + 1):
        result.setdefault(v, True)
    assert verify(clauses, result), "BUG: returned a non-satisfying model!"
    return "SAT", result, elapsed, num_vars, len(clauses)
 
def main():
    if len(sys.argv) != 2:
        print("Usage: python DPLL/dpll.py benchmarks/../xx.cnf")
        return
    with open(sys.argv[1]) as f:
        verdict, model, elapsed, nv, nc = solve_text(f.read())
    print(f"c file: {sys.argv[1]}  ({nv} vars, {nc} clauses)")
    print(f"c time: {elapsed:.4f} s")
    print("s " + ("SATISFIABLE" if verdict == "SAT" else "UNSATISFIABLE"))
    if model is not None:                        # DIMACS-style model line
        lits = [str(v if model[v] else -v) for v in sorted(model)]
        print("v " + " ".join(lits) + " 0")
 
 
if __name__ == "__main__":
    main()
