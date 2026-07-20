
// Purpose: Simulate a CDCL algorithm on SATLIB benchmark problems from University of British Columbia

/* General comments:
 * A lot of the indices for the vectors (notably assignments and trail_level) are indexed by literal.
 * Example 1: The literal "1" would have its value stored at assignment[1] and its trail level at trail_level[1].
 * Example 2: The literal "-3" would have its value stored at assignment[3] and its trail level at trail_level[3].
 * 
 * For the assignments, "0" indicates that the literal is unassigned while 1/-1 represents true/false respectively.
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

// TODO: Redo all relevant helper functions given that the CDCL uses a loop instead of recursion

/* Checks if a certain literal causes a conflict. If it does, returns the resolution clause.
 * Inputs:
 *      formula: Takes the formula from the main CDCL function.
 *      assignments: Holds the assignments.
 *      lit: The literal to check for conflict.
 * Output:
 *      Returns the resolution clause if a conflict occurs. Otherwise, returns a {0} clause.
 */
std::vector<int> checkConflict(const CNF &formula, const std::vector<int> &assignments, int lit) {
    int conflict1 = -1;
    int conflict2 = -1;

    for(int i = 0; i < formula.num_clauses; i++) {
        const std::vector<int> &clause = formula.clauses[i];
        auto begin = clause.begin();
        auto end = clause.end();

        bool pos = std::find(begin, end, lit) != end;
        bool neg = std::find(begin, end, -lit) != end;

        // If the literal does not exist in this clause, it can be skipped
        if((pos || neg) == false) continue;

        // If a clause that contains the literal is already satisfied or is unassigned, it can be skipped.
        bool flag = false;
        for(int x : clause) {
            if(x == lit || x == -lit) continue;

            int value = assignments[std::abs(x)];
            if(value == 0 || value == (x > 0 ? 1 : -1)) {
                flag = true;
                break;
            }
        }
        if(flag) continue;

        // Clause contains only the literal unassigned
        // TODO: Potential edgecase that a clause has both x and -x, making the indices be identical (hence the clause should be ignored)
        if(conflict1 == -1 && pos) conflict1 = i;
        if(conflict2 == -1 && neg) conflict2 = i;

        if(conflict1 != -1 && conflict2 != -1) break;
    }

    // Conflict is detected
    if(conflict1 != -1 && conflict2 != -1) {
        std::vector<int> resolution;

        const std::vector<int> &clause1 = formula.clauses[conflict1];
        const std::vector<int> &clause2 = formula.clauses[conflict2];

        for(int x : clause1) {
            if((x != lit && x != -lit) && (std::find(resolution.begin(), resolution.end(), x) == resolution.end())) resolution.push_back(x);
        }
        
        for(int x : clause2) {
            if((x != lit && x != -lit) && (std::find(resolution.begin(), resolution.end(), x) == resolution.end())) resolution.push_back(x);
        }

        return resolution;
    }

    // No conflict is detected (returns {0})
    return {0};
}

/* Performs unit propagation and processes conflict resolution. Returns the target_level from conflict resolution.
 * Inputs:
 *      formula: Takes the formula from the main CDCL function.
 *      assignments: Holds the assignments.
 *      trail: Holds the backtracking trail for the assignments.
 *      trail_level: Holds the guess levels for the backtracking trail.
 *      guess_level: Indicates the guess level of the current propagation.
 * Output:
 *      Returns the status of the evaluation:
 *          -1: Normal execution
 *          -2: Evaluation failed, should force a quit.
 *          >= 0: Conflict occurred, which stores the target level to backtrack to
 *      Modifies formula to include learned clauses, assignments to have new assignments, and trail to have the new backtracking trail.
 * 
 *      Note: An output of -2 can only happen if either the resolution clause is empty
 */
int unitPropagation(CNF &formula, std::vector<int> &assignments, std::vector<int> &trail,
    std::vector<int> trail_level, int guess_level) {

    // Unit Propagation
    while(true) {
        bool flag = true;
        for(int i = 0; i < formula.num_clauses; i++) {
            // Various flags to check the status of the clause.
            bool unsat = true;
            bool unit = false;
            int lit = 0;
            std::vector<int> &clause = formula.clauses[i];

            for(int x : clause) {
                int value = assignments[std::abs(x)];

                // If the clause is already satisfied (TODO: Could be optimized to have a separate tracker for which clauses are already satisfied?)
                // x = 0 should be impossible.
                if(value == (x > 0 ? 1 : -1)) {
                    unsat = false;
                    lit = -1;
                    break;
                }

                // If an unassigned literal is found, unsatisfiable is flagged to be false
                if(unsat && value == 0) unsat = false;

                // Stores the unassigned literal and flags as a unit clause when first unassigned literal is detected.
                if(lit == 0 && value == 0) {
                    unit = true;
                    lit = x;
                    continue;
                }

                // Unflags unit clause if another unassigned literal is detected
                if(unit && value == 0) {
                    unit = false;
                    continue;
                }
            }

            // Somehow there is an unsatisfiable clause
            if(unsat) return -2;

            // Unit clause found
            if(unit) {
                flag = false;
                std::vector<int> resolution = checkConflict(formula, assignments, lit);

                int size = resolution.size();

                // No conflict detected
                if(size == 1 && resolution[0] == 0) {
                    int index = std::abs(lit);
                    assignments[index] = (lit > 0 ? 1 : -1);
                    trail.push_back(index);
                    trail_level[index] = guess_level;
                    break;

                // Conflict detected
                } else {
                    int target_level = -2;
                    for(int x : resolution) {
                        int t = trail_level[std::abs(x)];
                        if(t > target_level) target_level = t;
                    }

                    // Updates the CNF
                    if(target_level != -2) {
                        formula.clauses.push_back(resolution);
                        formula.num_clauses++;
                    }

                    return target_level;
                }
            }
        }

        // Breaks loop if no more unit clauses are found
        if(flag) break;
    }

    return -1;
}

/* Runs the CDCL algorithm (but with a loop instead)
 * Inputs:
 *   formula: Takes the initial CNF that has literals from 1 to num_variables.
 *   assignments: Holds the assignments.
 * Output:
 *   Returns the verdict.
 */
bool CDCL(CNF formula, std::vector<int> &assignments) {
    // Stores the backtracking trail for the assignments
    std::vector<int> trail;
    std::vector<int> trail_level(formula.num_variables + 1);

    int guess_level = 0;  // Stores the guess level of the current propagation
    int target_level = 0; // Stores the guess level that needs to be pulled back to

    while (true) {
        int status = unitPropagation(formula, assignments, trail, trail_level, guess_level);

        // Unit propagation detects an unsat
        if(status == -2) return false;

        // Unit propagation runs into a conflict
        if(status >= 0) {
            
        }

        // Base Case 1: no clauses left means all clauses were satisfied
        // Base Case 2: an empty clause means this branch failed
        bool verdict = true;
        for (const auto& clause : formula.clauses) {
            if (clause.empty()) {
                flag = true;
                verdict = false;
                continue;
            }

            verdict = verdict && (clause.size() == 1 && clause[0] == 0);
        }

        if(verdict) return true;

        int lit = chooseFirstLiteral(formula);
        if(lit == 0) return false;


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
        bool verdict = initCDCL(reformat_formula, assignments);

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
