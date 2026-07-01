
// Purpose: Simulate a DPLL algorithm on SATLIB benchmark problems from University of British Columbia

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

// Simplifies the CNF when a certain variable is asserted true.
CNF simplify(const CNF& formula, int lit) {
    CNF newFormula;                                         // Creates a new CNF to store the simplified formula (fix(2))
    newFormula.num_variables = formula.num_variables;       // Copies the number of variables from the original formula (fix(2))
    newFormula.clauses.reserve(formula.clauses.size());     // Reserves space for the new clauses to avoid multiple allocations (fix(2))
    
    for (const auto& clause : formula.clauses) {
        bool satisfied = false;
        std::vector<int> newClause;
        newClause.reserve(clause.size());

        for (int x : clause) {
            if (x == lit) {
                satisfied = true;
                break;
            }

            if (x != -lit) {
                newClause.push_back(x);
            }
        }

        if (!satisfied) {
            newFormula.clauses.push_back(newClause);
        }
    }

    newFormula.num_clauses = newFormula.clauses.size();
    return newFormula;
}

/* Performs unit propagation
 * Inputs:
 *     formula: Takes the formula from the layer above.
 *     assignments: Stores the assignments. Uses a reference parameter to pass up the updated value.
 *     exit: Outputs whether or not the unit propagation detects an impossible CNF. Uses a reference parameter to pass up the updated value.
 *     changed: Outputs whether or not the assignments update. Uses a reference parameter to pass up the updated value.
 * Output:
 *     Returns the updated CNF
 */
CNF unitPropagation(CNF formula, std::unordered_map<int,int> &assignments, bool &exit) {
    while(true) {
        int var = 0;
        bool flag = false;
        for(int i = 0; i < formula.clauses.size(); i++) {
            // Empty clause -> Automatically fails
            if(formula.clauses[i].empty()) {
                exit = true;
                return formula;
            }
            
            // Unit clause -> Automatically assigned to satisfy equation
            if(formula.clauses[i].size() == 1) {
                var = formula.clauses[i][0];
                assignments[std::abs(var)] = (var > 0);
                flag = true;
                break;

                // Checks to see if the unit clause is NOT {0} (aka already satisfied)
                /*
                if(var != 0){
                    assignments.insert({std::abs(var), var > 0});
                    flag = true;
                    break;
                }
                */
            }
        }

        // Breaks loop if no more unit clauses are found
        if(!flag) {
            break;
        }

        formula = simplify(formula, var);
        // changed = true;
    }

    return formula;
}

/* Performs pure literal elimination
 * Inputs:
 *     formula: Takes the formula from the layer above.
 *     assignments: Stores the assignments. Uses a reference parameter to pass up the updated value.
 *     guess: Outputs a potential guess for the recursion algorithm to use. Uses a reference parameter to pass up the updated value.
 *     changed: Outputs whether or not the assignments update. Uses a reference parameter to pass up the updated value.
 * Output:
 *     Returns the updated CNF
 */
CNF pureLiteralElimination(CNF formula, std::unordered_map<int,int> &assignments) {
    std::vector<int> count;
    for(int i = 0; i < formula.clauses.size(); i++) {
        std::vector<int> clause = formula.clauses[i];
        for(int j = 0; j < clause.size(); j++) {
            int var = clause[j];

            // If not already in the count vector, pushes it into count
            if(std::find(count.begin(), count.end(), var) == count.end()) count.push_back(var);
        }
    }

    for(int i = 0; i < count.size(); i++) {
        int &var = count[i];

        // Skips if 0 (0 replaces failed checks for pure literals)
        if(var == 0) continue;

        auto check = std::find(count.begin(), count.end(), -var);
        if(check != count.end()) {                          // If the negative polarity is found, sets both the same and negative polarity values to 0 to skip later.
            var = 0;
            count[std::distance(count.begin(), check)] = 0;
        } else {                                            // If no negative polarity is found, sets the corresponding variable to positive.
            assignments.insert({std::abs(var), var > 0});
            formula = simplify(formula, var);
            // changed = true;
        }
    }

    return formula;
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

// Runs DPLL algorithm with the satisifiability of the formula being stored in verdict.
// Output is an unordered map of variables to values. (Works similarly to a Python dictionary)
// 0 represents negative, 1 represents positive
std::unordered_map<int,int> DPLL(CNF formula, bool &verdict) {
    // Initialize unordered map and temp CNF (to not modify the original)
    std::unordered_map<int,int> assignments;

    // Repeats unit propagation and pure literal elimination until neither change something.
    // Because both needs to be ran at least once before repeating, one iteration is done outside.
    // bool changed = false;
    bool exit = false;

    // formula = unitPropagation(formula, assignments, exit, changed);
    formula = unitPropagation(formula, assignments, exit);
    if(exit) {
        verdict = false;
        return assignments;
    }
    // formula = pureLiteralElimination(formula, assignments, changed);
    formula = pureLiteralElimination(formula, assignments);

    // while(true){
    //     if(!changed) break;
    //     changed = false;

    //     formula = unitPropagation(formula, assignments, exit, changed);
    //     if(exit) {
    //         verdict = false;
    //         return assignments;
    //     }

    //     if(!changed) break;
    //     changed = false;

    //     formula = pureLiteralElimination(formula, assignments, changed);
    // }

    // Base Case 1: no clauses left means all clauses were satisfied
    if (formula.clauses.empty()) {
        verdict = true;
        return assignments;
    }

    // Base Case 2: an empty clause means this branch failed
    for (const auto& clause : formula.clauses) {
        if (clause.empty()) {
            verdict = false;
            return assignments;
        }
    }


    // Recursion: Selects the first unassigned literal, then tries simplifying with both positive and negative inputs.
    int lit = chooseFirstLiteral(formula);

    if (lit == 0) {
        verdict = false;
        return assignments;
    }

    for (int g : {lit, -lit}) {
        bool v = false;

        CNF simplified = simplify(formula, g);
        std::unordered_map<int, int> a = DPLL(simplified, v);

        if (v) {
            verdict = true;
            a.insert({std::abs(g), g > 0});
            return a;
        }
    }

    verdict = false;
    return assignments;
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

// Command for generating dpll.exe: g++ -o dpll DPLL.cpp
// Command for running program: ./dpll "[X]", where X is the name of the file location of the dataset.
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

        bool verdict = false;
        std::unordered_map<int, int> assignments = DPLL(formula, verdict);

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
