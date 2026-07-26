
// Purpose: Simulate a CDCL algorithm on SATLIB benchmark problems from University of British Columbia
/* Version 2 changes: 
 *      Reworked the algorithm to work with vectors instead of unordered_maps
 *      Main algorithm runs with loops instead of recursion
 *      No longer mutates/copies the original CNF, instead using backtracking
 *      Uses a different conflict resolution algorithm (1-UIP)
 */

/* General comments:
 * A lot of the indices for the vectors (notably assignments and assignment_level) are indexed by literal.
 * Example 1: The literal "1" would have its value stored at assignment[1] and its trail level at assignment_level[1].
 * Example 2: The literal "-3" would have its value stored at assignment[3] and its trail level at assignment_level[3].
 * 
 * For the assignments, "0" indicates that the literal is unassigned while 1/-1 represents true/false respectively.
 * For the assignment levels, the value indicates the level. Has a default value of -1.
 * For the assignment reasons, the value indicates the clause index that resulted in the assignment. Has a default value of -2.
 * A value of -1 instead indicates that the assignment was from a decision.
 * 
 * For the trail, the backtracking is stored chronologically with the most recent changes being at the back of the vector.
 * The trail stores the literals that were assigned at certain times and may be undone by going from back to front.
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

/* Resolves a conflict that occurs at a given index. Performs backtracking, updates the guess level, and returns a flag.
 * Inputs:
 *      formula: Takes the formula from the main CDCL function.
 *      assignments: Holds the assignments.
 *      trail: Holds the backtracking trail.
 *      assignment_level: Holds the guess levels for given assignments.
 *      assignment_reason: Holds the clause index for the reason for corresponding assignments. -1 for any decisions.
 *      guess_level: The guess level of the current state.
 *      conflictIndex: The index of the clause that causes the conflict.
 * Output:
 *      Returns the status of conflict resolution:
 *          -1: Critical error of some sort, fails and executes program immediately.
 *          0: Conflict is resolved
 *          1: Unresolvable conflict is detected, should exit immediately.
 */
int resolveConflict(CNF &formula, std::vector<int> &assignments, std::vector<int> &trail, 
    std::vector<int> &assignment_level, std::vector<int> &assignment_reason, int &guess_level, int conflictIndex) {

    // Resolution clause
    std::vector<int> resolution = formula.clauses[conflictIndex];
    int count = 0;
    for(int x : resolution) {
        if(assignment_level[std::abs(x)] == guess_level) count++;
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

        const std::vector<int> &reasonClause = formula.clauses[assignment_reason[latest_lit]];

        // Deletes any instances of the latest assigned literal
        for(int i = 0; i < resolution.size(); i++) {
            int x = resolution[i];
            if(x == latest_lit || x == -latest_lit) {
                resolution[i] = resolution.back();
                resolution.pop_back();
                i--;
            }
        }

        for(int x : reasonClause) {
            if((x != latest_lit && x != -latest_lit) && (std::find(resolution.begin(), resolution.end(), x) == resolution.end())) resolution.push_back(x);
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

        // Backtracking
        while(!trail.empty()) {
            // Assume trail has only positive values.
            int var = trail.back();
            int tl = assignment_level[var];
            
            if(tl <= target_level) break;

            assignments[var] = 0;
            trail.pop_back();
            assignment_level[var] = -1;
            assignment_reason[var] = -2;
        }

        // If backtracked too far: Error
        if(trail.empty() && target_level > 0) {
            std::cout << "ERROR: Backtracking has reached an empty trail when target level is greater than 0" << std::endl;
            return -1;
        }

        // Assert learned clause value
        int index = std::abs(resolveLit);
        assignments[index] = resolveLit > 0 ? 1 : -1;
        trail.push_back(index);
        assignment_level[index] = target_level;
        assignment_reason[index] = formula.num_clauses - 1; // New resolution clause should be the one at the very back

        guess_level = target_level;

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
 * Output:
 *      Returns the status of the evaluation:
 *          -1: Critical error of some sort
 *          0: Normal execution
 *          1: Unit propagation results in an unresolvable conflict, should quit out.
 *      Modifies formula to include learned clauses, assignments to have new assignments, and trail to have the new backtracking trail.
 *      Note: Any modifications made as part of an incomplete unit propagation should be undone when doing conflict resolution.
 */
int unitPropagation(CNF &formula, std::vector<int> &assignments, std::vector<int> &trail,
    std::vector<int> &assignment_level, std::vector<int> &assignment_reason, int &guess_level) {

    // Unit Propagation
    while(true) {
        bool flag = true;
        for(int i = 0; i < formula.num_clauses; i++) {
            // Various flags to check the status of the clause.
            bool sat = false;
            int count = 0;
            int lit = 0;
            std::vector<int> &clause = formula.clauses[i];

            for(int x : clause) {
                int value = assignments[std::abs(x)];

                // If the clause is already satisfied (TODO: Could be optimized to have a separate tracker for which clauses are already satisfied?)
                // x = 0 should be impossible.
                if(value == (x > 0 ? 1 : -1)) {
                    sat = true;
                    break;
                }

                // Stores the unassigned literal and increments count (no purpose in keeping track of more literals past 1)
                if(count < 2 && value == 0) {
                    count++;
                    lit = x;
                }
            }

            if(sat) continue;

            // Unsatisfiable clause found, need to perform conflict resolution
            if(count == 0) {
                int status = resolveConflict(formula, assignments, trail, assignment_level, assignment_reason, guess_level, i);

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
                int index = std::abs(lit);
                assignments[index] = (lit > 0 ? 1 : -1);
                trail.push_back(index);
                assignment_level[index] = guess_level;
                assignment_reason[index] = i;

                flag = false;
                break;
            }
        }

        // Breaks loop if no more unit clauses are found
        if(flag) break;
    }

    return 0;
}

/* Chooses a literal to guess (TODO: Implement better heuristics using variable ordering and initial state selection)
 * Inputs:
 *   formula: Takes the initial CNF that has literals from 1 to num_variables.
 *   assignments: Holds the assignments.
 * Output:
 *   Returns the chosen literal.
 */
int chooseLiteral(const CNF &formula, const std::vector<int> &assignments) {
    // Simple naive heuristic
    for(const auto &clause : formula.clauses) {
        for(int x : clause) {
            if(assignments[std::abs(x)] == 0) return x;
        }
    }
    return 0;
}

/* Runs the CDCL algorithm (but with a loop instead)
 * Inputs:
 *   formula: Takes the initial CNF that has literals from 1 to num_variables.
 *   assignments: Holds the assignments.
 * Output:
 *   Returns the verdict.
 */
bool CDCL(CNF &formula, std::vector<int> &assignments) {
    // Stores the backtracking trail for the assignments
    std::vector<int> trail;
    std::vector<int> assignment_level(formula.num_variables + 1);
    std::vector<int> assignment_reason(formula.num_variables + 1);

    for(int i = 1; i <= formula.num_variables; i++) {
        assignment_level[i] = -1;
        assignment_reason[i] = -2;
    }

    int debug = 0; // DEBUG

    int guess_level = 0;  // Stores the guess level of the current propagation

    while (true) {
        int status = unitPropagation(formula, assignments, trail, assignment_level, assignment_reason, guess_level);

        // Critical error encountered
        if(status == -1) return false;

        // Unit propagation detects an unsat
        if(status == 1) return false;

        // Base Case 1: All clauses were satisfied
        // Base Case 2: An empty clause means this branch failed (should never run into in practice)
        // TODO: Stick into unit propagation instead?
        bool sat = true;
        bool unsat = false;
        for (const auto& clause : formula.clauses) {
            bool empty = true;
            bool flag = false;
            for(int x : clause) {
                int value = assignments[std::abs(x)];
                int polarity = x > 0 ? 1 : -1;
                
                // Checks to see if there is an empty (unsat) clause. Drops flag if it finds a term that is satisfied or unassigned.
                if(empty && (value == 0 || value == polarity)) empty = false;

                // Checks to see if there is at least one satisfied literal
                if(sat && !flag && value == polarity) flag = true;
            }

            if(empty) {
                unsat = true;
                break;
            }

            if(sat && !flag) sat = false;
        }

        // Checks unsat first, then sat
        if(unsat) return false;
        if(sat) return true;

        // Heuristics
        int lit = chooseLiteral(formula, assignments);
        if(lit == 0) { // Cannot find a literal
            std::cout << "ERROR: Cannot find unassigned literal" << std::endl;
            return false;
        }
        guess_level++;

        int index = std::abs(lit);
        assignments[index] = lit > 0 ? 1 : -1;
        trail.push_back(index);
        assignment_level[index] = guess_level;
        assignment_reason[index] = -1;

        // // DEBUG
        // printCNF(formula);
        // debug++;
        // if(debug == 20) return false;
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

// Command for generating cdcl.exe: g++ -o dpll DPLL.cpp
// Command for running program: ./cdcl "[X]", where X is the name of the file location of the dataset.
int main(int argc, char* argv[]) { // ChatGPT helped with capturing timing info
    if (argc != 2 && argc != 3) {
        std::cout << "Usage: ./dpll_cpp <benchmark_folder> [output_csv]" << std::endl;
        std::cout << "Example: ./dpll_cpp benchmarks/uf50-218 dpll_cpp_uf50_1000.csv" << std::endl;
        std::cout << "Example: ./dpll_cpp benchmarks/uuf50-218 dpll_cpp_uuf50_1000.csv" << std::endl;
        return 1;
    }

    std::string benchmarkFolder = argv[1];

    bool writeCSV = (argc == 3);
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

    for (const auto& filePath : files) {
        std::string filename = filePath.string();

        CNF formula = parseFile(filename);

        std::vector<int> key;
        CNF reformat_formula = reformat(formula, key);

        auto start = std::chrono::high_resolution_clock::now();

        std::vector<int> assignments(reformat_formula.num_variables + 1);
        bool verdict = CDCL(reformat_formula, assignments);

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

        if (writeCSV) {
            csv << filename << ","
                << elapsed_seconds << ","
                << verdictString << "\n";
        }

        std::cout << filename << "," << elapsed_seconds << "," << verdictString << std::endl;

        // // DEBUG
        // if(verdict == false) break;
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
    std::cout << "SAT count: " << satCount << std::endl;
    std::cout << "UNSAT count: " << unsatCount << std::endl;

    if (writeCSV) {
        std::cout << "Results written to " << argv[2] << std::endl;
    }

    return 0;
}
