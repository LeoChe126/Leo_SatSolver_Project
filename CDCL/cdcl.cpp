
// Purpose: Simulate a CDCL algorithm on SATLIB benchmark problems from University of British Columbia

// File parsing
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include <filesystem>

// DPLL algorithm
#include <chrono>
#include <unordered_map>
#include <cmath>
#include <algorithm>
#include <limits>

struct CNF {
    int num_variables = 0;
    int num_clauses = 0;
    std::vector<std::vector<int>> clauses;
};

// Simplifies the CNF when a certain variable is asserted true. If a conflict is encountered, returns the conflict indices.
void simplify(CNF &formula, int lit, int &conflict1, int &conflict2) {
    // CDCL: Undid most of the changes of fix(2) and replaced the .erase call in the previous DPLL implementation with swap-and-pop (if erase was causing that many issues)
    // CNF newFormula;                                         // Creates a new CNF to store the simplified formula (fix(2))
    // newFormula.num_variables = formula.num_variables;       // Copies the number of variables from the original formula (fix(2))
    // newFormula.clauses.reserve(formula.clauses.size());     // Reserves space for the new clauses to avoid multiple allocations (fix(2))

    // CDCL: Stores the indices of unit clauses of both polarities of lit.
    // If both conflict1 is not -1 and conflict2 is not -1, then a resolveable conflict has arisen.
    // If only conflict1 is not -1, that's impossible because unit propagation was run just before.
    // If only conflict2 is not -1, then it's just doing normal behavior (simplifying an enforced clause from unit propagation)
    conflict1 = -1;
    conflict2 = -1;
    
    for (int i = 0; i < formula.num_clauses; i++) {
        bool satisfied = false;
        std::vector<int> &clause = formula.clauses[i];
        // std::vector<int> newClause;

        for (int j = 0; j < clause.size(); j++) {
            int x = clause[j];
            if (x == lit) {
                satisfied = true;
                if(clause.size() == 1 && conflict2 == -1) conflict2 = i;
                break;
            }

            if (clause.size() == 1 && x == -lit && conflict1 == -1) conflict1 = i;

            if (x == -lit) {
                clause[j] = clause.back();
                clause.pop_back();
                j--;
            }

            if(conflict1 != -1 && conflict2 != -1) return; // If both conflicts are detected, breaks out of the function.
        }

        // if (!satisfied) {
        //     newFormula.clauses.push_back(newClause);
        // } else { // CDCL: Need to add this to keep the indices of the individual clauses for conflict resolution.
        //     newFormula.clauses.push_back({0});
        // }

        if(satisfied) { // CDCL: Need to add this to keep the indices of the individual clauses for conflict resolution.
            formula.clauses[i] = {0};
        }
    }
}

/* Performs unit propagation
 * Inputs:
 *     formula: Takes the formula from the layer above.
 *     assignments: Stores the assignments.
 *     exit: Outputs whether or not the unit propagation detects an impossible CNF.
 *     guess_level: Indicates the guess level of this current propagation.
 *     conflict1: Outputs the first index of the conflict (negative).
 *     conflict2: Outputs the second index of the conflict (positive).
 * Output:
 *     Returns the outcome of unit propagation
 *     0: Normal operation
 *     -1: Unit propagation fails normally
 *     >0: Conflict occurs with the literal as the output
 */
int unitPropagation(CNF &formula, std::unordered_map<int,int> &assignments, std::unordered_map<int,int> &level, int guess_level, int &conflict1, int &conflict2) {
    while(true) {
        int var = 0;
        bool flag = false;
        for(int i = 0; i < formula.clauses.size(); i++) {
            // Empty clause -> Automatically fails
            if(formula.clauses[i].empty()) return 1;
            
            // Unit clause -> Automatically assigned to satisfy equation
            if(formula.clauses[i].size() == 1) {
                var = formula.clauses[i][0];
                if(var != 0) { // CDCL: Added back the {0} checker since the index of clauses needs to be preserved.
                    assignments[std::abs(var)] = (var > 0);
                    level[std::abs(var)] = guess_level;
                    flag = true;
                    break;
                }
            }
        }

        // Breaks loop if no more unit clauses are found
        if(!flag) {
            break;
        }

        simplify(formula, var, conflict1, conflict2);
        if(conflict1 != -1) return std::abs(var);
    }

    return 0;
}

/* Performs conflict resolution.
 * Inputs:
 *     top: Gets the top of the assignments and inserts the resolution clause.
 *     level: Gets the levels of the assignments.
 *     lit: Gets the literal causing the conflict.
 *     guess_level: Gets the guess_level of the current iteration.
 * Output:
 *     Returns the target level for the resolution. If it is -1, then the learned clause is empty and the algorithm should stop immediately.
 */
int conflictResolution(CNF &top, const std::unordered_map<int,int> &level, int lit, int guess_level, int conflict1, int conflict2) {
    std::vector<int> clause1 = top.clauses[conflict1];
    std::vector<int> clause2 = top.clauses[conflict2];

    std::vector<int> resolution;

    for(int x : clause1) {
        if((x != lit && x != -lit) && (std::find(resolution.begin(), resolution.end(), x) == resolution.end())) resolution.push_back(x);
    }
    
    for(int x : clause2) {
        if((x != lit && x != -lit) && (std::find(resolution.begin(), resolution.end(), x) == resolution.end())) resolution.push_back(x);
    }

    if(resolution.size() == 0) {
        return -1;
    }

    top.clauses.push_back(resolution);

    int target_level = 0;

    for(int i = 0; i < resolution.size(); i++) {
        auto it = level.find(resolution[i]);
        if(it != level.end()) {
            int var = it->second;
            if(var > target_level && var < guess_level) {
                target_level = var;
            }
        }
    }

    return target_level;
}

// Helper function, replace that decision step with a direct scan for the first available nonzero literal. (Align with python implementation)
int chooseFirstLiteral(const CNF& formula) {    // fix(1): branching logic changed to select the first available literal (align with Python implementation)
    for (const auto& clause : formula.clauses) {
        for (int lit : clause) {
            if (lit != 0) {
                return lit;
            }
        }
    }

    return 0; // only happens if no decision literal exists
}

/* Runs the CDCL algorithm.
 * Inputs:
 *     formula: Takes the formula from the layer above.
 *     top: Holds the formula at the topmost layer. Relevant for conflict resolution.
 *     assignments: Holds the assignments.
 *     level: Holds the levels for the assignments.
 *     guess_level: Indicates the guess level of this current propagation.
 *     target_level: Outputs the guess level that needs to be pulled back
 *     conflict1: Outputs the first index of the conflict for conflict resolution (negative).
 *     conflict2: Outputs the second index of the conflict for conflict resolution (positive).
 * Output:
 *     Returns the verdict.
 */
bool CDCL(CNF formula, CNF &top, std::unordered_map<int,int> &assignments, std::unordered_map<int,int> &level, 
    int guess_level, int &target_level, int &conflict1, int &conflict2) {

    int status = unitPropagation(formula, assignments, level, guess_level, conflict1, conflict2);
    
    // CDCL: Unit propagation runs into a conflict
    if(status > 0) {
        target_level = conflictResolution(top, level, status, guess_level, conflict1, conflict2);
    }

    // Unit propagation fails (also includes conflict)
    if(status != 0) return false;

    // Base Case 1: no clauses left means all clauses were satisfied
    // Base Case 2: an empty clause means this branch failed
    bool verdict = true;
    for (const auto& clause : formula.clauses) {
        if (clause.empty()) return false;

        if(clause.size() != 1 || clause[0] != 0) verdict = false;
    }

    if(verdict) return true;

    // Recursion: Selects the first unassigned literal, then tries simplifying with both positive and negative inputs.
    int lit = chooseFirstLiteral(formula);

    if (lit == 0) return false;

    std::unordered_map<int,int> a = assignments;
    std::unordered_map<int,int> l = level;
    
    a.insert({std::abs(lit), lit > 0});
    l.insert({std::abs(lit), guess_level + 1});

    CNF simplified = formula;
    simplify(simplified, lit, conflict1, conflict2);
    bool v = CDCL(simplified, top, a, l, guess_level + 1, target_level, conflict1, conflict2);

    if (v) {
        assignments = a;
        return true;
    } else if(conflict1 != -1) { // CDCL: Conflict is detected
        if(target_level == -1) { // Learned clause is empty
            return false;
        } else if(guess_level == target_level) {
            // Adds all the learned clauses from top then simplifies using the current assignments
            int top_size = top.clauses.size();
            for(int i = formula.num_clauses; i < top_size; i++) {
                formula.clauses.push_back(top.clauses[i]);
                formula.num_clauses++;
            }

            for(const auto& pair : assignments) {
                simplify(formula, pair.first * (pair.second ? 1 : -1), conflict1, conflict2);
                if(conflict1 != -1) { // A new conflict shows up while trying to simplify
                    target_level = conflictResolution(top, level, status, guess_level, conflict1, conflict2);
                    return false;
                }
            }

            return CDCL(formula, top, assignments, level, guess_level, target_level, conflict1, conflict2);
        }
    }

    return false;
}

// Initializes the CDCL algorithm
bool initCDCL(CNF formula, std::unordered_map<int,int> assignments) {
    CNF top = formula;
    std::unordered_map<int,int> level;
    int target_level = 0;
    int conflict1, conflict2 = -1;
    return CDCL(formula, top, assignments, level, 0, target_level, conflict1, conflict2);
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


//const int MODE = 2; //Terminal inputs is now used to select the mode, no longer needed. 

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

        auto start = std::chrono::high_resolution_clock::now();

        std::unordered_map<int, int> assignments;
        bool verdict = initCDCL(formula, assignments);

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
