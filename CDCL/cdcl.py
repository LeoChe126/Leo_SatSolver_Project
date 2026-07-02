class CDCLSolver:
    def __init__(self, clauses):

        self.clauses = clauses
        self.assignment = {}  # variable -> True/False
        self.decision_level = 0
        self.implication_graph = []
        
    def solve(self):
        """
        Main CDCL solving algorithm.
        
        Returns True if satisfiable, False otherwise
        """
        self.decision_level = 0
        self.assignment = {}
        
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
        while changed:
            changed = False
            for clause in self.clauses:
                result = self.check_clause(clause)
                
                if result is False:  # Conflict
                    return clause
                
                if result is None:  # Unit clause
                    unassigned = self.get_unassigned_literal(clause)
                    if unassigned is not None:
                        var = abs(unassigned)
                        value = unassigned > 0
                        if var not in self.assignment:
                            self.assignment[var] = value
                            changed = True
        
        return None
    
    def check_clause(self, clause):
        """Check clause status: True, False, or None (unresolved)"""
        unassigned_count = 0
        
        for lit in clause:
            var = abs(lit)
            if var in self.assignment:
                if (lit > 0 and self.assignment[var]) or (lit < 0 and not self.assignment[var]):
                    return True  # Clause satisfied
            else:
                unassigned_count += 1
        
        return None if unassigned_count > 0 else False
    
    def get_unassigned_literal(self, clause):
        """Get unassigned literal in clause"""
        for lit in clause:
            if abs(lit) not in self.assignment:
                return lit
        return None
    
    def choose_variable(self):
        """Choose next variable to branch on"""
        for var in range(1, self.num_variables() + 1):
            if var not in self.assignment:
                return var
        return None
    
    def analyze_conflict(self, conflict):
        """Analyze conflict and determine backtrack level"""
        # Simplified: backtrack to decision_level - 1
        return max(0, self.decision_level - 1)
    
    def backtrack(self, level):
        """Backtrack to given decision level"""
        vars_to_remove = [v for v in self.assignment if v not in self.assignment]
        for var in vars_to_remove:
            del self.assignment[var]
    
    def num_variables(self):
        """Get number of variables"""
        max_var = 0
        for clause in self.clauses:
            for lit in clause:
                max_var = max(max_var, abs(lit))
        return max_var


# Example usage
if __name__ == "__main__":
    # (x1 OR x2) AND (NOT x1 OR x3) AND (NOT x2 OR NOT x3)
    clauses = [
        [1, 2],
        [-1, 3],
        [-2, -3]
    ]
    
    solver = CDCLSolver(clauses)
    result = solver.solve()
    print(f"Satisfiable: {result}")
    if result:
        print(f"Assignment: {solver.assignment}")
