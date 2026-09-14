
// Purpose: Simulate a CDCL algorithm on SATLIB benchmark problems from University of British Columbia
/* Version 2 changes: 
 *      Reworked the algorithm to work with vectors instead of unordered_maps
 *      Main algorithm runs with loops instead of recursion
 *      No longer mutates/copies the original CNF, instead using backtracking
 *      Uses a different conflict resolution algorithm (1-UIP)
 * Version 2.1 changes:
 *      Added tracking for various data points using a new struct
 *      Integrated the base case conditions for the main loop into the unit propagation
 *      Added a mode switcher for heuristics and added 2 new heuristics
 *      Updated a lot of comments
 * Version 2.2 changes:
 *      Made the assignments vector also store previous assignments using 2 and -2.
 *      Added a new heuristic which is a variant of highest unsigned freqeuncy. It uses the previous assignment if possible, otherwise identical to the original heuristic.
 *      Implemented VSIDS as a heuristic
 * Version 2.3 changes:
 *      Created a tracker for clause deletion using activity scores (similar to VSIDS)
 *      Implemented a two-watched-literals scheme for unit propagation
 *      Hijacked assignments[0] to keep track of total # of currently assigned literals
 * 
 * 
 * Current major TODO list:
 *      Try implementing a WalkSAT based heuristic
 *      Create a new version of clause culling that also accounts for clause size (maybe scale activity by 1 + 1/size?)
 *      Test the new version of two-watched-literals and record data
 */

/* General comments:
 * A lot of the indices for the vectors (notably assignments and assignment_level) are indexed by literal. The total number of assignments is stored at index 0.
 * Example 1: The literal "1" would have its value stored at assignment[1] and its trail level at assignment_level[1].
 * Example 2: The literal "-3" would have its value stored at assignment[3] and its trail level at assignment_level[3].
 * 
 * For the assignments, "0" indicates that the literal is unassigned while 1/-1 represents true/false respectively. 
 * 2/-2 are also unassigned, but store the last assignment used. The 0th index stores the number of currently assigned literals.
 * 
 * For the assignment levels, the value indicates the level. Has a default value of -1.
 * For the assignment reasons, the value indicates the clause index that resulted in the assignment. Has a default value of -2 and uses -1 for any decision.
 * A value of -1 instead indicates that the assignment was from a decision.
 * 
 * For the trail, the backtracking is stored chronologically with the most recent changes being at the back of the vector.
 * The trail stores the literals that were assigned at certain times and may be undone by going from back to front.
 * 
 * 
 * Notes about "tricks":
 * 
 * VSIDS: Considered to have worse decision quality than highest-frequency in exchange for much less overhead. However, hard to parallelize since the activity 
 *      has to be accessed and modified from multiple places.
 * Clause Culling: Helps keep the amount of memory consumed by resolution clauses under control. Slightly reduces efficiency, but its a pretty good way to make
 *      sure an excessive memory is not consumed. However, deletion being parallelly synchronized may be a bit of an issue (one dead cycle?)
 * Two-Watched-Literals: Saves an incredibly significant amount of overhead since the propagation function no longer scans all the clauses, which can become
 *      extremely massive for larger CNFs. Absolutely worth it if running on any large problem. Synchronizing the correct clause index may be a bit of an issue
 *      with clause culling though.
 */

// File parsing
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include <filesystem>

// CDCL algorithm
#include <chrono>
#include <utility>
#include <cmath>
#include <algorithm>
#include <limits>

struct CNF {
    int num_variables = 0;
    int num_clauses = 0;
    std::vector<std::vector<int>> clauses;
};

struct data {
    int num_decisions = 0;    // Total number of decisions made by heuristic
    int num_assignments = 0;  // Total number of unit propagation assignments
    int num_backtrack = 0;    // Total number of guess levels backtracked
    int num_resolutions = 0;  // Total number of resolution clauses added
    int num_culls = 0;        // Total number of resolution clauses culled
};

/* VSIDS: Contains all relevant VSIDS parameters. Gets updated whenever a value is unassigned due to backtracking.
 * active: Determines whether anything that interacts with VSIDS is active. Useful for runtime tests.
 * increment: Initial increment for the weight values for each literal.
 * RATIO: Geometric ratio of the increment every main loop cycle.
 * RESCALE_RATIO: Rescales the threshold by this value when the increment exceeds it.\
 * weight: Contains the weight values indexed by literal.
 * seen: Helper vector for keeping track of which literals to update in weights.
 */
struct VSIDS { // TODO: Use a variable heap?
    bool active = false;
    double increment = 0.5;

    const double RATIO = 1.2;
    const double RESCALE_RATIO = std::pow(10, 100);

    std::vector<double> weight;
    std::vector<bool> seen;
};

// Initialize VSIDS parameters using the frequency of literals in the original CNF
void initVSIDS(VSIDS &V, CNF formula) {
    V.weight = std::vector<double>(formula.num_variables + 1); // Should automatically initialize to zero
    V.seen = std::vector<bool>(formula.num_variables + 1);     // Should automatically initialize to false

    // Initialize weights to the unsigned frequency of literals
    // TODO: Mess around with the initial values, maybe try Jeruslow-Wang score?
    for(const auto &clause : formula.clauses) {
        for(int x : clause) {
            V.weight[std::abs(x)] += 1;
        }
    }
}

/* clauseActivity: Contains all relevant parameters for clause activity and culling. Used in culling at a geometrically decreasing frequency in the main loop.
 * active: Determines whether anything that interacts with clause activity is active. Useful for runtime tests.
 * increment: Initial increment for the activity values for each clause.
 * base_num_clauses: The original number of clauses in the CNF, used to index the activity vector properly.
 * RATIO: Geometric ratio of the increment every main loop cycle.
 * RESCALE_RATIO: Rescales the threshold by this value when the increment exceeds it.
 * activity: Contains the activity values for each resolution clause. The first index is the first resolution clause and all values start at 0.
 */
struct clauseActivity {
    bool active = false;
    double increment = 0.5;
    int base_num_clauses; // Stores the number of clauses that the CNF originally started with

    const double RATIO = 1.001;
    const double RESCALE_RATIO = std::pow(10, 20);
    const int THRESHOLD_INIT = 5;
    const int THRESHOLD_RATIO = 2;

    std::vector<double> activity; // Vector that holds the activity of clauses
};

/* TWL: Contains all relevant parameters for two-watched-literals. Used to heavily reduce overhead during unit propagation for larger CNFs.
 * active: Determines whether anything that uses TWL is active. Useful for runtime tests.
 * trailIndex: Holds the trail index that has been verified up to.
 * watched: Clauses that are watched by certain literals.
 * 
 * Notes about watched: 
 *  Indexed by literal, nonnegative clause indices are unchanged while negative clause indices are offset by 1. 
 *  Polarity used to reflect the literal polarity. All watched literals are in indices 0 or 1 for each clause.
 */
struct TWL {
    bool active = false;
    int trailIndex = 0;
    std::vector<std::vector<int>> watched;
};

/* Initializes TWL
 * Current Modes:
 *      1: TWL with the two literals being the first two in the clause
 *      2: TWL with the two literals prioritizing the most frequent literal using VSIDS initial values
 */
void initTWL(TWL &T, CNF formula, const VSIDS &V, const int T_MODE) {
    T.watched = std::vector<std::vector<int>>(formula.num_variables + 1);

    // Stores the first two literals in each clause in the watch list
    if(T_MODE == 1) {
        for(int i = 0; i < formula.num_clauses; i++) {\
            std::vector<int> &clause = formula.clauses[i];
            // Skips past empty clauses
            if(clause.size() == 0) continue;

            int value1 = clause[0];
            T.watched[std::abs(value1)].push_back((value1 > 0) ? i : -(i + 1));

            // Adds only one value to watch list for unit clause
            if(clause.size() == 1) continue;

            int value2 = clause[1];
            T.watched[std::abs(value2)].push_back((value2 > 0) ? i : -(i + 1));
        }
    } else if (T_MODE == 2) {
        if(V.active == false) {
            std::cout << "ERROR: VSIDS is not active. Running standard TWL initialization." << std::endl;
            initTWL(T, formula, V, 1);
            return;
        }

        for(int i = 0; i < formula.num_clauses; i++) {
            std::vector<int> &clause = formula.clauses[i];
            int size = clause.size();
            switch(size) {
                case 0: {} // Empty clause: Skip 
                case 1: {  // Unit clause: Watch the only literal
                    int value = clause[0];
                    T.watched[std::abs(value)].push_back((value > 0) ? i : -(i + 1));
                }
                case 2: {  // Binary clause: Watch both literals
                    int value1 = clause[0];
                    int value2 = clause[1];

                    T.watched[std::abs(value1)].push_back((value1 > 0) ? i : -(i + 1));
                    T.watched[std::abs(value2)].push_back((value2 > 0) ? i : -(i + 1));
                }
                default: {  // Choose the two most frequent literals and watch them
                    int index1, index2 = -1;
                    double weight1, weight2 = 0;

                    // Determine the two most frequent literals in the clause
                    for(int i = 0; i < size; i++) {
                        int index = std::abs(clause[i]);
                        int weight = V.weight[index];

                        if(index1 == -1) {
                            index1 = i;
                            weight1 = weight;
                        } else if(index2 == -1 || weight > weight2) {
                            if(weight > weight1) {
                                index2 = index1;
                                weight2 = weight1;

                                index1 = i;
                                weight1 = weight;
                            } else {
                                index2 = i;
                                weight2 = weight;
                            }
                        }
                    }

                    int lit1 = clause[index1];
                    int lit2 = clause[index2];

                    // Add both literals to watch list
                    T.watched[std::abs(lit1)].push_back((lit1 > 0) ? i : -(i + 1));
                    T.watched[std::abs(lit2)].push_back((lit2 > 0) ? i : -(i + 1));

                    // Rearrange CNF such that the two watched literals are first and second respectively
                    clause[index1] = clause[0];
                    clause[0] = lit1;

                    clause[index2] = clause[1];
                    clause[1] = lit2;
                }
            }
        }
    }
}

// Function for debugging
void printCNF(const CNF &formula) {
    for(int i = 0; i < formula.num_clauses; i++) {
        const auto &clause = formula.clauses[i];
        std::cout << "Clause " << i << ": ";
        for(int j = 0; j < clause.size(); j++) {
            std::cout << clause[j];
            if(j != clause.size() - 1) {
                std::cout << ", ";
            }
        }
        std::cout << "." << std::endl;
    }
}

// Simple helper function to assign a certain literal to its polarity
void assignLiteral(std::vector<int> &assignments, std::vector<int> &trail, std::vector<int> &assignment_level, std::vector<int> &assignment_reason,
    int &guess_level, int lit, int reason) {
    
    int index = std::abs(lit);
    assignments[0]++; // V2.3: Increments total assignment counter
    assignments[index] = lit > 0 ? 1 : -1;
    trail.push_back(index);
    assignment_level[index] = guess_level;
    assignment_reason[index] = reason;
}

/* Resolves a conflict that occurs at a given index. Performs backtracking, updates the guess level, and returns a flag.
 * Inputs:
 *      formula: Takes the formula from the main CDCL function.
 *      assignments: Holds the assignments.
 *      trail: Holds the backtracking trail.
 *      assignment_level: Holds the guess levels for given assignments.
 *      assignment_reason: Holds the clause index for the reason for corresponding assignments. -1 for any decisions.
 *      guess_level: The guess level of the current state.
 *      conflictIndex: The index of the clause that causes the conflict.
 *      d: Tracks data
 * Output:
 *      Returns the status of conflict resolution:
 *          -1: Critical error of some sort, fails and executes program immediately.
 *          0: Conflict is resolved
 *          1: Unresolvable conflict is detected, should exit immediately.
 */
int resolveConflict(CNF &formula, std::vector<int> &assignments, std::vector<int> &trail, 
    std::vector<int> &assignment_level, std::vector<int> &assignment_reason, int &guess_level, 
    int conflictIndex, VSIDS &V, clauseActivity &CA, TWL &T, data &d) {

    // Resolution clause
    std::vector<int> resolution = formula.clauses[conflictIndex];
    int count = 0;
    
    std::vector<int> updateVSIDS; // V2.2
    for(int i = 0; i < resolution.size(); i++) {
        int index = std::abs(resolution[i]);
        if(assignment_level[index] == guess_level) count++;

        // V2.2: Updating VSIDS seen vector
        if(V.active && V.seen[index] == false) {
            V.seen[index] = true;
            updateVSIDS.push_back(index);
        }
    }

    while(count > 1) {
        int latest_lit = 0;
        int index = -1;
        for(int i = 0; i < resolution.size(); i++) {
            int var = std::abs(resolution[i]);
            if(assignment_level[var] == guess_level && assignment_reason[var] != -1) {
                int trail_index = (std::find(trail.begin(), trail.end(), var) - trail.begin());

                if(trail_index == trail.size()) {
                    std::cout << "ERROR: Recent assignment not found on trail" << std::endl;
                    return -1;
                }

                if(trail_index > index) {
                    latest_lit = var;
                    index = trail_index;
                }
            }
        }

        if(index == -1) {
            std::cout << "ERROR: No propagated assignments found despite having more than one literal assigned at current level." << std::endl;
            return -1;
        }

        int reasonIndex = assignment_reason[latest_lit];
        const std::vector<int> &reasonClause = formula.clauses[reasonIndex];

        // V2.3: If the reason clause is a learned clause, then the appropriate activity is increased
        if(CA.active && reasonIndex >= CA.base_num_clauses) {
            // Can assume that there is a value initialized because the activity is created whenever a new clause is added.
            CA.activity[reasonIndex - CA.base_num_clauses] += CA.increment;
        }

        // Deletes any instances of the latest assigned literal
        for(int i = 0; i < resolution.size(); i++) {
            int x = resolution[i];
            if(x == latest_lit || x == -latest_lit) {
                resolution[i] = resolution.back();
                resolution.pop_back();
                i--;
            }
        }

        // Merges with the reason clause
        for(int x : reasonClause) {
            if((x != latest_lit && x != -latest_lit) && (std::find(resolution.begin(), resolution.end(), x) == resolution.end())) resolution.push_back(x);

            // V2.2: Updating VSIDS seen vector, ensuring that no duplicates occur.
            if(V.active) {
                int i = std::abs(x);
                if(V.seen[i] == false) {
                    V.seen[i] = true;
                    updateVSIDS.push_back(i);
                }
            }
        }

        // Recounts number of literals at current guess level
        count = 0;
        for(int x : resolution) {
            if(assignment_level[std::abs(x)] == guess_level) count++;
        }
    }

    // Obtain target level 
    int target_level = -1;
    // Obtain literal to be resolved (should be assigned to something after this loop)
    int resolveLit = 0;

    // If resolution clause is size 1, target_level is 0.
    if(resolution.size() == 1) {
        // Asserts a unit clause when already at guess level 0, unsat
        if(guess_level == 0) return 1;

        target_level = 0;
        resolveLit = resolution[0];
    } else if (resolution.size() == 0) return 1; // If resolution clause is size 0, then unsat.
    else {
        for(int x : resolution) {
            int t = assignment_level[std::abs(x)];
            if(t > target_level && t < guess_level) target_level = t;
            if(t == guess_level) resolveLit = x;
        }
    }

    // Updates the CNF + Backtracking
    if(target_level != -1) {
        formula.clauses.push_back(resolution);
        formula.num_clauses++;
        d.num_resolutions++;

        // V2.3: Initializes activity value for new clause
        if(CA.active) CA.activity.push_back(CA.increment);

        // V2.3: Adds first two literals as watched literals (only adds one watched literal if unit clause)
        if(T.active) {
            for(int i = 0; i < resolution.size(); i++) {
                T.watched[std::abs(resolution[i])].push_back(resolution[i] > 0 ? formula.num_clauses - 1 : -formula.num_clauses);

                if(i == 1) break;
            }
        }

        // Backtracking
        while(!trail.empty()) {
            // Assume trail has only positive values.
            int var = trail.back();
            int tl = assignment_level[var];
            
            if(tl <= target_level) break;

            assignments[0]--; // V2.3: Decrements total assignment counter
            assignments[var] = assignments[var] > 0 ? 2 : -2; // V2.2: Now resets to 2/-2 depending on previous assignment
            trail.pop_back();
            assignment_level[var] = -1;
            assignment_reason[var] = -2;
            d.num_backtrack++;

            // V2.3: Backtrack trail index for TWL if necessary
            if(T.active && trail.size() < T.trailIndex) T.trailIndex = trail.size();
        }

        // If backtracked too far: Error
        if(trail.empty() && target_level > 0) {
            std::cout << "ERROR: Backtracking has reached an empty trail when target level is greater than 0" << std::endl;
            return -1;
        }

        guess_level = target_level;

        // Assert learned clause value
        assignLiteral(assignments, trail, assignment_level, assignment_reason, guess_level, resolveLit, formula.num_clauses - 1);

        // V2.2: Updates VSIDS parameters after resolution
        if(V.active) {
            if(V.increment > V.RESCALE_RATIO) { // Safety for overflow
                V.increment /= V.RESCALE_RATIO;
                for(int i = 0; i < V.weight.size(); i++) { 
                    V.weight[i] /= V.RESCALE_RATIO;
                }
            }

            for(int x : updateVSIDS) {
                V.weight[x] += V.increment;
                V.seen[x] = false;
            }
            V.increment *= V.RATIO;
        }

        // V2.3: Update clause activity parameters after resolution
        if(CA.active) {
            if(CA.increment >= CA.RESCALE_RATIO) { // Safety for overflow 
                CA.increment /= CA.RESCALE_RATIO;
                for(int i = 0; i < CA.activity.size(); i++) {
                    CA.activity[i] /= CA.RESCALE_RATIO;
                }
            }
            CA.increment *= CA.RATIO;
        }

        // Conflict resolution complete
        return 0;
    } 
    // If no target level was found and the resolution clause was created (aka tries to backtrack before forced assignments)
    // Note: An empty resolution clause also falls through to this result, which is expected.
    return 1;
}

/* Performs unit propagation until no unit clauses are found. Also checks for any unsat clauses and attempts to resolve them.
 * Inputs:
 *      formula: Takes the formula from the main CDCL function.
 *      assignments: Holds the assignments.
 *      trail: Holds the backtracking trail.
 *      assignment_level: Holds the guess levels for given assignments
 *      assignment_reason: Holds the clause index for the reason for corresponding assignments. -1 for any decisions.
 *      guess_level: Indicates the guess level of the current propagation.
 *      d: Stores the tracking data
 * Output:
 *      Returns the status of the evaluation:
 *          -1: Critical error of some sort
 *          0: Normal execution
 *          1: Unit propagation results in an unresolvable conflict, should quit out.
 *          2: Unit propagation finds a fully satisfied CNF, should quit out.
 *      Modifies formula to include learned clauses, assignments to have new assignments, and trail to have the new backtracking trail.
 *      Note: Any modifications made as part of an incomplete unit propagation should be undone when doing conflict resolution.
 */
int unitPropagation(CNF &formula, std::vector<int> &assignments, std::vector<int> &trail,
    std::vector<int> &assignment_level, std::vector<int> &assignment_reason, int &guess_level, 
    VSIDS &V, clauseActivity &CA, TWL &T, data &d) {

    // V2.3 Unit propagation (TWL)
    if(T.active) {
        // Trail index is at 0, which only occurs at startup
        if(T.trailIndex == 0) {
            // Scans for purely unit clauses
            for(int i = 0; i < formula.num_clauses; i++) {
                const std::vector<int> &clause = formula.clauses[i];
                if(clause.size() == 1) {
                    if(assignments[std::abs(clause[0])] == (clause[0] > 0 ? -1 : 1)) return 1; // Unsat if two unit clauses clash with each other

                    if(assignments[std::abs(clause[0])] == (clause[0] > 0 ? 1 : -1)) continue; // Skips reassignment if already assigned
                    assignLiteral(assignments, trail, assignment_level, assignment_reason, guess_level, clause[0], i);
                    d.num_assignments++;
                }
            }
        }

        while(T.trailIndex < trail.size()) {
            int index = trail[T.trailIndex];
            T.trailIndex++;
            std::vector<int> &watch = T.watched[index];

            // The literal has been recently assigned and needs to be checked
            int assignment = assignments[index];
            if(assignment == -1 || assignment == 1) {
                for(int i = 0; i < watch.size(); i++) {
                    int rawIndex = watch[i];
                    // Polarity matches: Ignore this clause
                    if((rawIndex >= 0 && assignment > 0) || (rawIndex < 0 && assignment < 0)) continue;

                    // Current watch literal is falsified
                    int clauseIndex = (rawIndex >= 0) ? rawIndex : -rawIndex - 1;
                    std::vector<int> &clause = formula.clauses[clauseIndex];

                    bool flag = true;
                    int currentWatchIndex = 0;
                    for(int j = 0; j < clause.size(); j++) {
                        int value = clause[j];
                        int valueIndex = std::abs(value);
                        if(j < 2) { // Watched literals
                            // Other watched literal is already satisfied: Ignore this clause
                            if(valueIndex != index && assignments[valueIndex] == (value > 0 ? 1 : -1)) {
                                flag = false;
                                break;
                            }

                            // Currently on watched literal
                            if(valueIndex == index) currentWatchIndex = j;
                        } else { // Other literals, scanning for a potential other literal to use
                            if(assignments[valueIndex] != (value > 0 ? -1 : 1)) { // An unassigned/satisifed literal is found, swap places
                                // Removing the old watched literal
                                watch[i] = watch.back();
                                watch.pop_back();
                                i--;

                                // Adding the new watched literal
                                T.watched[valueIndex].push_back(value > 0 ? clauseIndex : -(clauseIndex + 1));

                                // Swapping around the literals in the clause
                                clause[j] = clause[currentWatchIndex];
                                clause[currentWatchIndex] = value;

                                flag = false;
                                break;
                            }
                        }
                    }

                    // No watched literal is currently satisfied and no replacement watched literal is available
                    if(flag) {
                        if(clause.size() != 1) {
                            int otherWatch = clause[!currentWatchIndex]; // currentWatchIndex can only be 0 or 1
                            int value = assignments[std::abs(otherWatch)];
                            if(value != -1 && value != 1) { // Since there is no replacement, the other watched variable must be assigned if possible
                                assignLiteral(assignments, trail, assignment_level, assignment_reason, guess_level, otherWatch, clauseIndex);
                                d.num_assignments++;
                                continue;
                            }
                        }

                        // If code reaches this point, a conflict occurred.
                        int status = resolveConflict(formula, assignments, trail, assignment_level, assignment_reason, guess_level, clauseIndex, V, CA, T, d);

                        // If conflict is successfully resolved, tries propagation again.
                        if(status == 0) break;

                        // Falls through if a critical error occurs or an unresolvable conflict is detected.
                        return status;
                    }
                }
            } else {
                std::cout << "ERROR: Trail contains an assignment that doesn't exist" << std::endl;
                return -1;
            }
        }

        // All varaibles assigned without conflict = fully satisfied
        if(assignments[0] == formula.num_variables) return 2;
        return 0;
    } else { // Unit propagation (naive)
        while(true) {
            bool allSat = true;
            bool flag = true;
            for(int i = 0; i < formula.num_clauses; i++) {
                // Various flags to check the status of the clause.
                bool sat = false;
                int count = 0;
                int lit = 0;
                std::vector<int> &clause = formula.clauses[i];

                for(int x : clause) {
                    int value = assignments[std::abs(x)];

                    // If the clause is already satisfied 
                    // TODO: Could have a separate tracker for which clauses are already satisfied?
                    // Apparently two-watched literals implements this idea but better.
                    if(value == (x > 0 ? 1 : -1)) {
                        sat = true;
                        break;
                    }

                    // Stores the unassigned literal and increments count (no purpose in keeping track of more literals past 1)
                    if(count < 2 && (value != -1 && value != 1)) { // V2.2: Right condition originally checked value == 0
                        count++;
                        lit = x;
                    }
                }

                if(sat) continue;

                // Unsatisfiable clause found, need to perform conflict resolution
                if(count == 0) {
                    int status = resolveConflict(formula, assignments, trail, assignment_level, assignment_reason, guess_level, i, V, CA, T, d);

                    // If conflict is successfully resolved, tries propagation again.
                    if(status == 0) {
                        flag = false;
                        break;
                    }

                    // Falls through if a critical error occurs or an unresolvable conflict is detected.
                    return status;
                }

                // Unit clause found
                if(count == 1) {
                    assignLiteral(assignments, trail, assignment_level, assignment_reason, guess_level, lit, i);
                    d.num_assignments++;

                    flag = false;
                    break;
                }

                // A clause is not satisfied. (This flag does not need to be kept track of if any of the above if statements are triggered since a new propagation starts)
                allSat = false;
            }

            // Breaks loop if no more unit clauses are found
            if(flag) {
                if(allSat) return 2;

                return 0;
            }
        }
    }

    // Fallout return statement
    return 0;
}

/* Chooses a literal to guess
 * Inputs:
 *      formula: Takes the CNF.
 *      assignments: Holds the assignments.
 *      d: Stores the tracking data
 * Output:
 *      Returns the chosen literal.
 * 
 * Current Modes:
 *      0: Simple naive heuristic, chooses first unassigned literal found
 *      1: Highest unassigned unsigned literal frequency. Always returns a positive literal.
 *      2: Highest unassigned signed literal frequency.
 *      3: Highest unassigned unsigned literal frequency. Uses previous assignment if available. Otherwise, chooses the polarity with higher frequency.
 *      4: VSIDS with a default positive polarity if not previously assigned.
 */
int chooseLiteral(const CNF &formula, const std::vector<int> &assignments, const int H_MODE, VSIDS &V) {
    switch(H_MODE) {
        case 0: { // Simple naive heuristic
            for(const auto &clause : formula.clauses) {
                for(int x : clause) {
                    int value = assignments[std::abs(x)];
                    if(value != -1 && value != 1) return x; // V2.2: Condition originally only checked for value == 0
                }  
            }
            return 0;
        }

        case 1: { // Highest unassigned literal frequency (unsigned, biased towards more frequent polarity, positive if tied) 
                  // TODO: Don't like how it creates a new vector each time. Better way of tracking?
            int lit = 0;
            int maxCount = 0;
            std::vector<int> posCounts(formula.num_variables + 1);
            std::vector<int> negCounts(formula.num_variables + 1);
            for(const auto &clause : formula.clauses) {
                for(int x : clause) {
                    int value = assignments[std::abs(x)];
                    if(value == -1 || value == 1) continue; // V2.2: Condition originally only checked for value == 0
                    int l = std::abs(x);

                    if(x > 0) {
                        posCounts[l]++;
                    } else {
                        negCounts[l]++;
                    }

                    int c = posCounts[l] + negCounts[l];

                    if(c > maxCount) {
                        lit = (posCounts[l] >= negCounts[l] ? l : -l);
                        maxCount = c;
                    }
                }
            }
            return lit;
        }

        case 2: { // Highest unassigned literal frequency (signed) TODO: Same situation as case above but twice as bad.
            int lit = 0;
            int maxCount = 0;
            std::vector<int> posCounts(formula.num_variables + 1);
            std::vector<int> negCounts(formula.num_variables + 1);
            for(const auto &clause : formula.clauses) {
                for(int x : clause) {
                    int value = assignments[std::abs(x)];
                    if(value == -1 || value == 1) continue; // V2.2: Condition originally only checked for value == 0
                    int c;

                    if(x > 0) {
                        c = ++posCounts[x];
                    } else {
                        c = ++negCounts[-x];
                    }

                    if(c > maxCount) {
                        lit = x;
                        maxCount = c;
                    }
                }
            }
            return lit;
        }

        case 3: { // Highest unassigned literal frequency (unsigned, uses previous assignment if available, biased towards more frequent polarity, positive if tied) 
                  // TODO: Same issue as mode 1
            int lit = 0;
            int maxCount = 0;
            std::vector<int> posCounts(formula.num_variables + 1);
            std::vector<int> negCounts(formula.num_variables + 1);
            for(const auto &clause : formula.clauses) {
                for(int x : clause) {
                    int value = assignments[std::abs(x)];
                    if(value == -1 || value == 1) continue; // V2.2: Condition originally only checked for value == 0
                    int l = std::abs(x);

                    if(x > 0) {
                        posCounts[l]++;
                    } else {
                        negCounts[l]++;
                    }

                    int c = posCounts[l] + negCounts[l];

                    if(c > maxCount) {
                        lit = (posCounts[l] >= negCounts[l] ? l : -l);
                        maxCount = c;
                    }
                }
            }

            int prev = assignments[std::abs(lit)];
            if(prev == -2 || prev == 2) {
                return (prev > 0 ? std::abs(lit) : -std::abs(lit));
            }
            return lit;
        }

        case 4: { // VSIDS, uses default value of positive polarity
            int lit = 0;
            double maxWeight = -1.0;

            for(int i = 1; i <= formula.num_variables; i++) {
                int value = assignments[i];
                if(value != -1 && value != 1) {
                    double currentWeight = V.weight[i];
                    if(currentWeight > maxWeight) {
                        maxWeight = currentWeight;
                        if(value == 0) {
                            lit = -i;
                        } else {
                            lit = (value > 0 ? i : -i);
                        }
                    }
                }
            }

            return lit;
        }

        default:
            std::cout << "ERROR: Unknown heuristic mode chosen" << std::endl;
            break;
    }

    // Fallout return (for default case)
    return 0;
}

/* Culls resolution clauses based on culling mode. Does not consider binary/unit clauses or 
 * clauses involved in current iteration.
 * Inputs:
 *      formula: Takes the CNF.
 *      trail: Uses the trail to determine which literals have been modified recently.
 *      assignment_reason: Uses the assignment reason and the trail to determine which clauses are part of the current trail. Updates if necessary.
 *      d: Stores the tracking data.
 * Output:
 *      Returns an error message, 0 indicates normal operation.
 * 
 * Current Modes:
 *      0: Default, does nothing.
 *      1: Clause culling culls the bottom half of clause activity
 */
int clauseCulling(CNF &formula, const std::vector<int> &trail, std::vector<int> &assignment_reason,
    const int C_MODE, clauseActivity &CA, TWL &T, data &d) {
    switch(C_MODE) {
        case 0: { return 0; }
        case 1: {
            std::vector<int> candidates;
            int base_num_clauses = CA.base_num_clauses; // Starting point for resolution clauses

            // Select all non-binary and non-unit clauses
            for(int i = base_num_clauses; i < formula.num_clauses; i++) {
                if(formula.clauses[i].size() > 2) candidates.push_back(i);
            }

            // Remove all clauses part of the trail
            std::vector<int> used;
            for(int x : trail) {
                int val = assignment_reason[x];
                // In theory, the trail should only contain assignment reasons of -1 (decision) or a nonnegative number (clause)
                if(val != -2 && val != -1) {
                    used.push_back(val);
                }
            }

            for(int i = 0; i < candidates.size(); i++) {
                int index = std::find(used.begin(), used.end(), candidates[i]) - used.begin();
                if(index != used.end() - used.begin()) {
                    candidates[i] = candidates.back();
                    candidates.pop_back();
                    i--;
                }
            }

            // Extract activity values corresponding to the candidates vector
            std::vector<double> activity;
            for(int x : candidates) {
                activity.push_back(CA.activity[x - base_num_clauses]);
            }

            // Sort activities and corresponding clause indices to be ascending. Bottom half will be culled.
            // TODO: Use a better sorting algorithm? Currently uses bubble sort
            bool flag = true;
            while(flag) {
                flag = false;
                for(int i = 0; i + 1 < activity.size(); i++) {
                    if(activity[i] > activity[i + 1]) {
                        int temp1 = candidates[i];
                        double temp2 = activity[i];
                        candidates[i] = candidates[i + 1];
                        activity[i] = activity[i + 1];
                        candidates[i + 1] = temp1;
                        activity[i + 1] = temp2;
                        flag = true;
                    }
                }
            }

            // Cull bottom half of resolution clauses
            int cutoff = candidates.size() / 2;
            for(int i = 0; i < cutoff; i++) {
                int last_index = --formula.num_clauses;

                // Clause to be deleted is the last clause
                if(candidates[i] == last_index) {
                    formula.clauses.pop_back();
                    CA.activity.pop_back();
                } else { // Clause to be deleted is in the middle (swap-and-pop with more steps)
                    formula.clauses[candidates[i]] = formula.clauses[last_index];
                    formula.clauses.pop_back();

                    CA.activity[candidates[i] - base_num_clauses] = CA.activity[last_index - base_num_clauses];
                    CA.activity.pop_back();
                }

                // Updating any assignment reasons if the clause was rearranged
                for(int j = 0; j < assignment_reason.size(); j++) {
                    if(assignment_reason[j] == last_index) {
                        assignment_reason[j] = candidates[i];
                    }
                }

                // Updating any watched clauses for TWL
                if(T.active) {
                    for(int j = 0; j < T.watched.size(); j++) {
                        std::vector<int> &clauseList = T.watched[j];

                        for(int k = 0; k < clauseList.size(); k++) {
                            int raw_index = clauseList[k];
                            int converted_index = raw_index >= 0 ? raw_index : -raw_index - 1;

                            // Clause matches the one that needs to be culled: should be removed
                            if(converted_index == candidates[i]) {
                                clauseList[k] = clauseList.back();
                                clauseList.pop_back();
                                k--;
                            } else if(converted_index == last_index) { // Clause is the clause that was just moved: should be updated
                                clauseList[k] = raw_index >= 0 ? candidates[i] : -(candidates[i] + 1);
                            }
                        }
                    }
                }

                // Updating any candidates for culling if the clause was rearranged
                // TODO: Optimize to not double-tread over candidates
                for(int j = 0; j < cutoff; j++) {
                    if(candidates[j] == last_index) {
                        candidates[j] = candidates[i];
                    }
                }
            }

            d.num_culls += cutoff;

            return 0;
        }

        default:
            std::cout << "ERROR: Unknown culling mode chosen" << std::endl;
            break;
    }

    // Fallout return (for default case)
    return 1;
}

/* Runs the CDCL algorithm (but with a loop instead)
 * Inputs:
 *      formula: Takes the initial CNF that has literals from 1 to num_variables.
 *      assignments: Holds the assignments.
 *      d: Stores the tracking data
 * Output:
 *      Returns the verdict.
 */
bool CDCL(CNF &formula, std::vector<int> &assignments, const int H_MODE, const int C_MODE, 
    VSIDS &V, clauseActivity &CA, TWL &T, data &d) {
    // Stores the backtracking trail for the assignments
    std::vector<int> trail;
    std::vector<int> assignment_level(formula.num_variables + 1);
    std::vector<int> assignment_reason(formula.num_variables + 1);

    for(int i = 1; i <= formula.num_variables; i++) {
        assignment_level[i] = -1;
        assignment_reason[i] = -2;
    }

    int guess_level = 0;  // Stores the guess level of the current propagation

    // V2.3: Added a counter so that some of the resolution clauses are culled every couple of iterations.
    int count = 0;
    int threshold = CA.THRESHOLD_INIT;

    while (true) {
        int status = unitPropagation(formula, assignments, trail, assignment_level, assignment_reason, guess_level, V, CA, T, d);

        // Critical error encountered
        if(status == -1) return false;

        // Unit propagation detects an unsat
        if(status == 1) return false;

        // Unit propagation detects a fully satisfied CNF
        if(status == 2) return true;

        // Heuristics
        int lit = chooseLiteral(formula, assignments, H_MODE, V);
        if(lit == 0) { // Cannot find a literal
            std::cout << "ERROR: Cannot find unassigned literal" << std::endl;
            return false;
        }
        guess_level++;
        d.num_decisions++;

        assignLiteral(assignments, trail, assignment_level, assignment_reason, guess_level, lit, -1);

        // V2.3: Invokes clause culling and geometrically increments the threshold
        if(CA.active) {
            count++;
            if(count >= threshold) {
                count = 0;
                int log = clauseCulling(formula, trail, assignment_reason, C_MODE, CA, T, d);
                if(log == 1) return false; // Break out if an error is picked up
                threshold *= CA.THRESHOLD_RATIO;
            }
        }

        // DEBUG
        // if (d.num_resolutions % 200 == 0) {
        //     std::cout << "conflicts=" << d.num_resolutions
        //                 << " clauses=" << formula.num_clauses
        //                 << " culls=" << d.num_culls
        //                 << " level=" << guess_level
        //                 << std::endl;
        // }
    }
    // If the loop somehow exits, return false (this should never happen)
    return false;
}

// Copied from AI, modified slightly for clarity
CNF parseFile(const std::string& filename) {
    std::ifstream infile(filename);
    CNF formula;
    
    if (!infile.is_open()) {
        std::cerr << "Error: Could not open file " << filename << std::endl;
        return formula;
    }

    std::string line;
    std::vector<int> current_clause;

    while (std::getline(infile, line)) {
        // Trim leading/trailing whitespace
        size_t start = line.find_first_not_of(" \t\r\n");
        if (start == std::string::npos) {
            continue;
        }

        size_t end = line.find_last_not_of(" \t\r\n");
        line = line.substr(start, end - start + 1);

        // Skip empty lines
        if (line.empty()){
            continue;
        }

        if (line[0] == 'c') {
            continue;
        }

        if (line[0] == '%') {
            continue;
        }

        if (line == "0") {
            continue;
        }

        std::istringstream iss(line);
        char type;
        iss >> type;

        // Skip comment lines
        // Problem line: p cnf [num_vars] [num_clauses]
        if (type == 'p') {
            std::string format;
            iss >> format >> formula.num_variables >> formula.num_clauses;
            formula.clauses.reserve(formula.num_clauses); // Optimize memory allocations
        }
        // It's a clause definition line
        else {
            // Put the char back since it's part of the first integer literal
            iss.putback(type);
            
            int literal;
            while (iss >> literal) {
                if (literal == 0) {
                    // 0 marks the end of the current clause
                    formula.clauses.push_back(current_clause);
                    current_clause.clear();
                } else {
                    current_clause.push_back(literal);
                }
            }
        }
    }

    // Edge case: Some CNF variations omit the trailing '0' on the absolute last line
    if (!current_clause.empty()) {
        formula.clauses.push_back(current_clause);
    }

    formula.num_clauses = formula.clauses.size();
    
    return formula;
}

// Reformats the CNF to a more usable form. Example: (1, 2, 3) instead of (1, 6, 3)
// Returns the key by pass-by-reference, which can be used to map the original literals to the reformatted ones
// The key index represents what literal is used to represent it (index of 0 goes to 1, index of 1 goes to 2, etc.)
CNF reformat(const CNF formula, std::vector<int> &key) {
    CNF newFormula;
    newFormula.num_variables = formula.num_variables;
    newFormula.num_clauses = formula.num_clauses;

    for(int i = 0; i < formula.num_clauses; i++) {
        std::vector<int> newClause;
        
        for(int j = 0; j < formula.clauses[i].size(); j++) {
            int lit = formula.clauses[i][j];
            auto it = std::find(key.begin(), key.end(), std::abs(lit));
            int index = std::distance(key.begin(), it);

            if(it == key.end()) {
                key.push_back(std::abs(lit));
            }
            newClause.push_back((index + 1) * (lit > 0 ? 1 : -1));
        }

        newFormula.clauses.push_back(newClause);
    }

    return newFormula;
}

// Prints the assignments, properly converted back into their original form.
void printAssignments(const std::vector<int> &assignments, const std::vector<int> &key) {
    std::cout << "Assignments:" << std::endl;
    for(int i = 1; i < assignments.size(); i++) {
        std::cout << key[i - 1] << ": " << assignments[i] << std::endl;
    }
}

// Verifies the assignments validity.
bool verifyAssignments(const CNF &formula, const std::vector<int> &assignments, int num_clauses) {
    for(int i = 0; i < num_clauses; i++) {
        bool flag = false;
        const std::vector<int> &clause = formula.clauses[i];

        for(int j = 0; j < clause.size(); j++) {
            int lit = clause[j];
            int value = assignments[std::abs(lit)];
            if(value == (lit > 0 ? 1 : -1)) {
                flag = true;
                break;
            }
        }

        if(!flag) return false;
    }

    return true;
}

// Command for generating cdcl.exe: g++ -o cdcl_v2 CDCL_V2.cpp
// Command for running program: ./cdcl "[X]", where X is the name of the file location of the dataset.
int main(int argc, char* argv[]) { // ChatGPT helped with capturing timing info
    if (argc < 2 || argc > 6) {
        std::cout << "Usage: ./cdcl_v2 <benchmark_folder> [output_csv] [heuristic_mode] [culling_mode]" << std::endl;
        std::cout << "Example: ./cdcl_v2 benchmarks/uf50-218 cdcl_v2_cpp_uf50_1000.csv 0 0" << std::endl;
        std::cout << "Example: ./cdcl_v2 benchmarks/uuf50-218 cdcl_v2_cpp_uuf50_1000.csv 0 0" << std::endl;
        return 1;
    }

    std::string benchmarkFolder = argv[1];

    bool writeCSV = (argc >= 3);
    int heuristic_mode = (argc >= 4 ? std::atoi(argv[3]) : 0);
    int culling_mode = (argc >= 5 ? std::atoi(argv[4]) : 0);
    int TWL_mode = (argc >= 6 ? std::atoi(argv[5]) : 0);
    std::ofstream csv;

    if (writeCSV) {
        csv.open(argv[2]);
        csv << "file,time,verdict\n";
    }

    std::vector<std::filesystem::path> files;

    for (const auto& entry : std::filesystem::directory_iterator(benchmarkFolder)) {
        if (entry.is_regular_file() && entry.path().extension() == ".cnf") {
            files.push_back(entry.path());
        }
    }

    std::sort(files.begin(), files.end());

    if (files.empty()) {
        std::cout << "ERROR: No .cnf files found in " << benchmarkFolder << std::endl;
        return 1;
    }

    int numSolved = 0;
    int satCount = 0;
    int unsatCount = 0;

    double minTime = std::numeric_limits<double>::max();
    double maxTime = 0.0;
    double totalTime = 0.0;

    int totalDecisions = 0;
    int totalAssignments = 0;
    int totalBacktrack = 0;
    int totalResolutions = 0;
    int totalCulls = 0;

    const int NUM_FILES = 100;

    for (const auto& filePath : files) {
        std::string filename = filePath.string();

        CNF formula = parseFile(filename);

        auto start = std::chrono::high_resolution_clock::now();

        std::vector<int> key;
        CNF reformat_formula = reformat(formula, key);

        // Initializes and toggles VSIDS
        VSIDS V;
        if(heuristic_mode == 4) {
            initVSIDS(V, reformat_formula);
            V.active = true;
        }

        // Initializes and toggles clause activity
        clauseActivity CA;
        if(culling_mode == 1) {
            CA.base_num_clauses = reformat_formula.num_clauses;
            CA.active = true;
        }

        // Initializes and toggles TWL
        TWL T;
        if(TWL_mode != 0) {
            initTWL(T, reformat_formula, V, TWL_mode);
            T.active = true;
        }

        data d;

        std::vector<int> assignments(reformat_formula.num_variables + 1);
        bool verdict = CDCL(reformat_formula, assignments, heuristic_mode, culling_mode, V, CA, T, d);

        auto end = std::chrono::high_resolution_clock::now();

        double elapsed_seconds =
            std::chrono::duration_cast<std::chrono::microseconds>(end - start).count() / 1000000.0;

        std::string verdictString = verdict ? "SATISFIABLE" : "UNSATISFIABLE";

        numSolved++;
        totalTime += elapsed_seconds;

        if (elapsed_seconds < minTime) {
            minTime = elapsed_seconds;
        }

        if (elapsed_seconds > maxTime) {
            maxTime = elapsed_seconds;
        }

        if (verdict) {
            satCount++;
        } else {
            unsatCount++;
        }

        totalDecisions += d.num_decisions;
        totalAssignments += d.num_assignments;
        totalBacktrack += d.num_backtrack;
        totalResolutions += d.num_resolutions;
        totalCulls += d.num_culls;

        if (writeCSV) {
            csv << filename << ","
                << elapsed_seconds << ","
                << verdictString << "\n";
        }

        std::cout << filename << "," << elapsed_seconds << "," << verdictString << std::endl;
        
        // DEBUG
        // std::cout << "Assignment validity: " << verifyAssignments(reformat_formula, assignments, formula.num_clauses) << std::endl;
        // printAssignments(assignments, key);

        if(numSolved != -1 && numSolved >= NUM_FILES) break;
    }

    if (writeCSV) {
        csv.close();
    }

    double avgTime = totalTime / numSolved;

    std::cout << std::endl;
    std::cout << "num solved: " << numSolved << std::endl;
    std::cout << "min time: " << minTime << std::endl;
    std::cout << "max time: " << maxTime << std::endl;
    std::cout << "avg time: " << avgTime << std::endl;

    std::cout << std::endl;
    std::cout << "avg decisions: " << 1.0 * totalDecisions / numSolved << std::endl;
    std::cout << "avg assignments: " << 1.0 * totalAssignments / numSolved << std::endl;
    std::cout << "avg backtracks: " << 1.0 * totalBacktrack / numSolved << std::endl;
    std::cout << "avg resolutions: " << 1.0 * totalResolutions / numSolved << std::endl;
    std::cout << "avg culls: " << 1.0 * totalCulls / numSolved << std::endl;

    std::cout << std::endl;
    std::cout << "SAT count: " << satCount << std::endl;
    std::cout << "UNSAT count: " << unsatCount << std::endl;

    if (writeCSV) {
        std::cout << "Results written to " << argv[2] << std::endl;
    }

    return 0;
}
