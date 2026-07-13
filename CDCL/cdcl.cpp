
// Purpose: Simulate a CDCL algorithm on SATLIB benchmark problems from University of British Columbia

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

/* Checks if a certain assignment causes a conflict. If it does, returns the resolution clause.
 * Inputs:
 *      formula: Takes the formula from the main CDCL function.
 *      assignments: Holds the assignments.
 *      lit: The literal to check for conflict.
 * Output:
 *      Returns the resolution clause if a conflict occurs. Otherwise, returns an empty clause.
 */
std::vector<int> checkConflict(const CNF &formula, const std::vector<int> &assignments, int lit) {
    std::vector<int> resolution;

    

    return resolution;
}

/* Evaluates the CNF, performing unit propagation and conflict resolution.
 * Inputs:
 *      formula: Takes the formula from the main CDCL function.
 *      assignments: Holds the assignments.  
 *      trail: Holds the backtracking trail for the assignments.
 *      trail_level: Holds the guess levels for the backtracking trail.
 *      guess_level: Indicates the guess level of the current propagation
 * Output:
 *      Returns the status of the evaluation:
 *          0: Normal execution
 *          -1: Evaluation failed without conflict
 *          >0: Conflict occurred, which stores the target level to backtrack to
 *      Modifies formula to include learned clauses, assignments to have new assignments,
 *      and trail to have the new backtracking trail.
 */
int evaluateCNF(CNF &formula, std::vector<int> &assignments, std::vector<std::pair<int,int>> &trail,
    std::vector<int> trail_level, int guess_level) {

    int conflict1 = -1;
    int conflict2 = -1;

    while(true) {
        int var = 0;
        bool flag = true;
        for(int i = 0; i < formula.clauses.size(); i++) {
            vector<int> &clause = formula.clauses[i]
            for(int j = 0; j < clause.size(); j++) {

            }
            // Clause is satisfied, skip to next clause
            
        }

        // Breaks loop if no more unit clauses are found
        if(!flag) {
            break;
        }
    }

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
    std::vector<std::pair<int,int>> trail;
    std::vector<int> trail_level;

    int guess_level = 0;            // Stores the guess level of the current propagation
    int target_level = 0;           // Stores the guess level that needs to be pulled back to (TODO: Implement backtracking)
    int conflict1, conflict2 = -1;  // Stores the indices of the conflict for conflict resolution (negative, positive)
    bool flag = false;              // Stores whether or not a conflict has been detected

    while (true) {
        int status = unitPropagation(formula, assignments, level, guess_level, conflict1, conflict2);

        // CDCL: Unit propagation runs into a conflict
        if(status > 0) {
            target_level = conflictResolution(formula, level, status, guess_level, conflict1, conflict2);
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

        std::vector<int> assignments;
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
