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
        # Clause minimization counter
        self.num_clause_literals_removed = 0

        # for UNSAT optimization
        self.num_restarts = 0
        self.restart_base = 1000
        self.luby_index = 1
        self.conflicts_at_last_restart = 0

        self.clauses = clauses

        #for clause reduction
        self.active = [True] * len(self.clauses)
        self.clause_is_learned = [False] * len(self.clauses)
        self.clause_activity = [0.0] * len(self.clauses)
        self.learned_clause_indices = []
        self.clause_id_to_index = {id(clause): idx for idx, clause in enumerate(self.clauses)}

        self.num_clause_reductions = 0
        self.num_deleted_clauses = 0

        # Tune later
        self.reduce_interval = 1000
        
        self.next_reduce = 10000
        self.reduce_inc = 5000
        

        #LBD calculation
        self.clause_lbd = [0] * len(self.clauses)

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
    
   
    def initial_propagate(self): 
        # initial pass for unit clauses before the main ccl loop, still scans all clauses once
        seeds = []
        changed = True 
        while changed: 
            changed = False 
            for ci, clause in enumerate(self.clauses): 
                if not self.active[ci]: #uses only active clauses.
                    continue 
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

                #learned_idx = self.add_learned_clause(learned) 
                old_len = len(learned)
                learned = self.minimize_learned_clause(learned) # learned clause reduction, temporarily disabled for testing
                new_len = len(learned)
                self.num_clause_literals_removed += old_len - new_len
                backtrack_level = self.compute_backjump_level(learned)
                learned_idx = self.add_learned_clause(learned)

                if self.num_conflicts > 0 and self.num_conflicts % self.reduce_interval == 0:
                    self.reduce_clause_database()
                                
                """
                # for cdcl restart 
                if self.num_conflicts >= self.next_restart:
                    self.backtrack(0)
                    self.decision_level = 0
                    self.num_restarts += 1
                    self.next_restart += self.restart_interval
                    conflict = self.propagate([])
                    continue
                """
                
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
                """
                if (self.num_conflicts - self.conflicts_at_last_restart) >= self.restart_base * self._luby(self.luby_index):
                    self.conflicts_at_last_restart = self.num_conflicts
                    self.luby_index += 1
                    self.num_restarts += 1
                    self.backtrack(0)
                    self.decision_level = 0
                    conflict = None
                    continue
                """
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

                if not self.active[ci]: #deleted learned clauses may still appear in watchlists, but the solver will ignore them
                    continue

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
        self.bump_clause_activity(conflict_clause)

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
                self.bump_clause_activity(reason_clause) # makes recently useful learned clauses less likely to be deleted.
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
    
    #for luby restart
    def _luby(self, i):
        # 1-indexed Luby: 1,1,2,1,1,2,4,1,1,2,1,1,2,4,8,...
        k = 1
        while True:
            if i == (1 << k) - 1:
                return 1 << (k - 1)
            elif (1 << (k - 1)) <= i < (1 << k) - 1:
                i = i - (1 << (k - 1)) + 1
                k = 1
            else:
                k += 1
    
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
    
    # helper function for clause minimization
    '''
    def minimize_learned_clause(self, learned): ######################################### LOOK CAREFULLY FOR THIS FUNCTION
        """
        keep the asserting literal, 
        which is assumed to be the last literal in the learned clause. 
        for each non asserting literal, try to remove it if the reason clause is 
        already covered by variables in the learned clause.
        This is a simple minimizer helper function that does not remove all possible redundant literals yet, 
        for the correctness
        """
        if len(learned) <= 1:
            return learned

        clause_vars = set(abs(l) for l in learned)
        cache = {}

        def redundant(lit):
            var = abs(lit)
            r = self.reason[var]
            if r is None:
                return False
            for q in r:
                qv = abs(q)
                if qv == var:            continue
                if qv in clause_vars:    continue
                if self.level[qv] == 0:  continue
                if qv in cache:
                    if cache[qv]: continue
                    return False
                if self.reason[qv] is not None and redundant(q):
                    cache[qv] = True; continue
                cache[qv] = False
                return False
            return True
        asserting = learned[-1]
        minimized = []
        for lit in learned[:-1]:
            if self.reason[abs(lit)] is None:
                minimized.append(lit)
            elif redundant(lit):
                self.num_clause_literals_removed += 1
            else:
                minimized.append(lit)
        minimized.append(asserting)      # asserting literal MUST stay last
        return minimized
    '''
    
    def minimize_learned_clause(self, learned): 
        
        if len(learned) <= 2:
            return learned
        
        asserting_lit = learned[-1]
        learned_vars = set(abs(lit) for lit in learned)

        minimized = []
        for lit in learned[:-1]:
            var = abs(lit)
            reason_clause = self.reason[var]

            # Decision literals cannot be minimized using reason clauses
            if reason_clause is None:
                minimized.append(lit)
                continue

            redundant = True

            for rlit in reason_clause:
                rvar = abs(rlit)

                # Skip the variable we are trying to remove
                if rvar == var:
                    continue

                # If the reason depends on a variable not already in learned,
                # then removing lit may be unsafe.
                if rvar not in learned_vars:
                    redundant = False
                    break

            if not redundant:
                minimized.append(lit)

        # Always keep asserting literal
        minimized.append(asserting_lit)

        return minimized
    

    def compute_backjump_level(self, learned):
        """
        Compute the backjump level for a learned clause.

        Assumes learned[-1] is the asserting literal.
        Backjump level is the highest decision level among all other literals.
        """

        if not learned:
            return -1

        asserting_var = abs(learned[-1])
        backjump_level = 0

        for lit in learned:
            var = abs(lit)

            if var == asserting_var:
                continue

            backjump_level = max(backjump_level, self.level[var])

        return backjump_level

    def compute_lbd(self, clause):
        """
        LBD/glue score:
        number of distinct decision levels appearing in this clause.
        Lower LBD is usually better.
        """
        levels = set()

        for lit in clause:
            v = abs(lit)
            levels.add(self.level[v])

        return len(levels)

    # helper function for clause activity bumping
    def bump_clause_activity(self, clause):
        """
        Increase activity of a learned clause when it participates in conflict analysis.
        """

        ci = self.clause_id_to_index.get(id(clause))

        if ci is None:
            return

        if not self.clause_is_learned[ci]:
            return

        self.clause_activity[ci] += 1.0
    
    # learned clause is “locked” if it is currently the reason for some assignment.
    def is_locked_clause(self, ci):
        """
        A clause is locked if it is currently used as a reason for an assignment.
        Locked clauses should not be deleted.
        """

        target_id = id(self.clauses[ci])

        for reason_clause in self.reason:
            if reason_clause is not None and id(reason_clause) == target_id:
                return True

        return False
    
    ''''''
    def reduce_clause_database(self):
        """
        Logically delete low-activity learned clauses.

        Simple policy:
        - never delete original clauses
        - never delete binary clauses
        - never delete locked clauses
        - delete half of remaining learned clauses with lowest activity
        """

        candidates = []

        for ci in self.learned_clause_indices:
            if not self.active[ci]:
                continue

            clause = self.clauses[ci]

            # Keep short clauses because they are usually valuable
            if len(clause) <= 2:
                continue

            # Keep glue clauses
            if self.clause_lbd[ci] <= 2:
                continue

            # Do not delete clauses currently used as reasons
            if self.is_locked_clause(ci):
                continue

            candidates.append(ci)

        if len(candidates) < 10:
            return

        # Low activity first; for equal activity, delete longer clauses first
        candidates.sort(key=lambda ci: (-self.clause_lbd[ci], self.clause_activity[ci], -len(self.clauses[ci])))

        delete_count = len(candidates) // 4 #quarter of candidates to delete, can be tuned later. 

        for ci in candidates[:delete_count]:
            self.active[ci] = False
            self.num_deleted_clauses += 1

        self.num_clause_reductions += 1
    ''''''

    def reduce_clause_database(self):
        locked = set()
        for r in self.reason:
            if r is not None:
                locked.add(id(r))
        candidates = []
        for ci in self.learned_clause_indices:
            if not self.active[ci]:            continue
            clause = self.clauses[ci]
            if len(clause) <= 2:               continue
            if self.clause_lbd[ci] <= 2:       continue
            if id(clause) in locked:           continue
            candidates.append(ci)
        if len(candidates) < 10:
            return
        candidates.sort(key=lambda ci: (self.clause_lbd[ci], -self.clause_activity[ci]),
                        reverse=True)
        delete_count = len(candidates) // 4
        for ci in candidates[:delete_count]:
            self.active[ci] = False
            self.num_deleted_clauses += 1
        self.num_clause_reductions += 1

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
        """
        Add learned clause and initialize its two watched literals.
        Returns the new clause index.
        """

        self.clauses.append(clause)
        ci = len(self.clauses) - 1

        self.watch1.append(-1)
        self.watch2.append(-1)

        self.active.append(True)
        self.clause_is_learned.append(True)
        self.clause_activity.append(1.0)
        self.clause_lbd.append(self.compute_lbd(clause))
        self.learned_clause_indices.append(ci)
        self.clause_id_to_index[id(clause)] = ci

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

def walksat_with_restarts(
    clauses,
    num_vars,
    max_total_steps=1000,
    restart_after_no_improve=200,
    noise=0.3,
    seed=None
):
    start_time = time.perf_counter()
    rng = random.Random(seed)

    global_best_assignment = None
    global_best_unsat = float("inf")

    total_steps = 0
    restarts = 0
    trap_count = 0

    best_found_at_restart = 0
    best_found_at_step = 0
    hit_solution = False

    while total_steps < max_total_steps:
        restarts += 1

        assignment = [None] + [rng.choice([True, False]) for _ in range(num_vars)]

        local_best_unsat, unsat_indices = count_unsatisfied_clauses(clauses, assignment)
        no_improve_steps = 0

        if local_best_unsat < global_best_unsat:
            global_best_unsat = local_best_unsat
            global_best_assignment = assignment[:]
            best_found_at_restart = restarts
            best_found_at_step = total_steps

        while total_steps < max_total_steps:
            current_unsat_count, unsat_indices = count_unsatisfied_clauses(
                clauses,
                assignment
            )

            if current_unsat_count == 0:
                global_best_assignment = assignment[:]
                global_best_unsat = 0
                hit_solution = True

                elapsed = time.perf_counter() - start_time

                stats = {
                    "walksat_time": elapsed,
                    "walksat_total_steps": total_steps,
                    "walksat_restarts": restarts,
                    "walksat_best_unsat_count": global_best_unsat,
                    "walksat_hit_solution": int(hit_solution),
                    "walksat_trap_count": trap_count,
                    "walksat_best_found_at_restart": best_found_at_restart,
                    "walksat_best_found_at_step": best_found_at_step,
                }

                return global_best_assignment, global_best_unsat, stats

            if current_unsat_count < local_best_unsat:
                local_best_unsat = current_unsat_count
                no_improve_steps = 0

                if current_unsat_count < global_best_unsat:
                    global_best_unsat = current_unsat_count
                    global_best_assignment = assignment[:]
                    best_found_at_restart = restarts
                    best_found_at_step = total_steps
            else:
                no_improve_steps += 1

            if no_improve_steps >= restart_after_no_improve:
                trap_count += 1
                break

            clause_idx = rng.choice(unsat_indices)
            clause = clauses[clause_idx]

            if rng.random() < noise:
                lit = rng.choice(clause)
                flip_var = abs(lit)

            else:
                best_flip_var = None
                best_flip_unsat = float("inf")

                for lit in clause:
                    var = abs(lit)

                    assignment[var] = not assignment[var]
                    new_unsat_count, _ = count_unsatisfied_clauses(clauses, assignment)
                    assignment[var] = not assignment[var]

                    if new_unsat_count < best_flip_unsat:
                        best_flip_unsat = new_unsat_count
                        best_flip_var = var

                flip_var = best_flip_var

            assignment[flip_var] = not assignment[flip_var]
            total_steps += 1

    elapsed = time.perf_counter() - start_time

    if global_best_assignment is None:
        global_best_assignment = [None] + [rng.choice([True, False]) for _ in range(num_vars)]

    stats = {
        "walksat_time": elapsed,
        "walksat_total_steps": total_steps,
        "walksat_restarts": restarts,
        "walksat_best_unsat_count": global_best_unsat,
        "walksat_hit_solution": int(hit_solution),
        "walksat_trap_count": trap_count,
        "walksat_best_found_at_restart": best_found_at_restart,
        "walksat_best_found_at_step": best_found_at_step,
    }

    return global_best_assignment, global_best_unsat, stats


#Helper functions to solve a single file and adding timeout per file for large datasat (UF/UUF 250-1065) 
def solve_one_file(args):
    filepath, mode, file_index = args

    with open(filepath) as f:
        num_vars, clauses = parseFile(f.read())

    initial_assignment = None

    walksat_stats = {
        "walksat_time": "",
        "walksat_total_steps": "",
        "walksat_restarts": "",
        "walksat_best_unsat_count": "",
        "walksat_hit_solution": "",
        "walksat_trap_count": "",
        "walksat_best_found_at_restart": "",
        "walksat_best_found_at_step": "",
    }

    full_start = time.perf_counter()

    if mode == "baseline":
        initial_assignment = None

    elif mode == "random":
        initial_assignment = random_phase_assignment(num_vars, seed=file_index)

    elif mode == "walksat":
        initial_assignment, walksat_unsat_count, walksat_stats = walksat_with_restarts(
            clauses,
            num_vars,
            max_total_steps=1000,
            restart_after_no_improve=200,
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

    cdcl_start = time.perf_counter()
    result = solver.solve()
    cdcl_time = time.perf_counter() - cdcl_start

    total_time = time.perf_counter() - full_start

    verdict = "SATISFIABLE" if result else "UNSATISFIABLE"

    return {
        "file": filepath,
        "mode": mode,
        "time": cdcl_time,
        "cdcl_time": cdcl_time,
        "total_time": total_time,
        "verdict": verdict,

        "decisions": solver.num_decisions,
        "conflicts": solver.num_conflicts,
        "propagations": solver.num_propagations,
        "learned": solver.num_learned,

        # Clause minimization/deletion counters
        "clause_literals_removed": solver.num_clause_literals_removed,
        "clause_reductions": solver.num_clause_reductions,
        "deleted_clauses": solver.num_deleted_clauses,

        # WalkSAT counters
        "walksat_time": walksat_stats["walksat_time"],
        "walksat_total_steps": walksat_stats["walksat_total_steps"],
        "walksat_restarts": walksat_stats["walksat_restarts"],
        "walksat_best_unsat_count": walksat_stats["walksat_best_unsat_count"],
        "walksat_hit_solution": walksat_stats["walksat_hit_solution"],
        "walksat_trap_count": walksat_stats["walksat_trap_count"],
        "walksat_best_found_at_restart": walksat_stats["walksat_best_found_at_restart"],
        "walksat_best_found_at_step": walksat_stats["walksat_best_found_at_step"],

        #CDCL restart counter
        "restarts": solver.num_restarts,
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
                "cdcl_time": "",
                "total_time": "",
                "verdict": "TIMEOUT",

                "decisions": "",
                "conflicts": "",
                "propagations": "",
                "learned": "",
                "restarts": "",

                "clause_literals_removed": "",
                "clause_reductions": "",
                "deleted_clauses": "",

                "walksat_time": "",
                "walksat_total_steps": "",
                "walksat_restarts": "",
                "walksat_best_unsat_count": "",
                "walksat_hit_solution": "",
                "walksat_trap_count": "",
                "walksat_best_found_at_restart": "",
                "walksat_best_found_at_step": "",

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

    times = []
    sat = unsat = timeouts = errors = 0
    tot_conf = tot_dec = tot_prop = tot_learn = 0

    csv_file = open(output_csv, "w") if output_csv else None
    if csv_file:
        csv_file.write(
            "file,mode,cdcl_time,total_time,verdict,"
            "decisions,conflicts,propagations,learned,restarts,"
            "clause_literals_removed,clause_reductions,deleted_clauses,"
            "walksat_time,walksat_total_steps,walksat_restarts,"
            "walksat_best_unsat_count,walksat_hit_solution,walksat_trap_count,"
            "walksat_best_found_at_restart,walksat_best_found_at_step\n"
        )

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
                    f"{row.get('file','')},{row.get('mode','')},{row.get('cdcl_time','')},{row.get('total_time','')},{row.get('verdict','')},"
                    f"{row.get('decisions','')},{row.get('conflicts','')},{row.get('propagations','')},{row.get('learned','')},{row.get('restarts','')},"
                    f"{row.get('clause_literals_removed','')},{row.get('clause_reductions','')},{row.get('deleted_clauses','')},"
                    f"{row.get('walksat_time','')},{row.get('walksat_total_steps','')},{row.get('walksat_restarts','')},"
                    f"{row.get('walksat_best_unsat_count','')},{row.get('walksat_hit_solution','')},{row.get('walksat_trap_count','')},"
                    f"{row.get('walksat_best_found_at_restart','')},{row.get('walksat_best_found_at_step','')}\n"
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



###############################################################################################################################################################################################
