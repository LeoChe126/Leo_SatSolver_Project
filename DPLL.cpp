
// Purpose: Simulate a DPLL algorithm on SATLIB benchmark problems from University of British Columbia

// File parsing
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>

// DPLL algorithm
#include <chrono>
#include <unordered_map>
#include <cmath>
#include <algorithm>

struct CNF {
    int num_variables = 0;
    int num_clauses = 0;
    std::vector<std::vector<int>> clauses;
};

// Simplifies the CNF when a certain variable is asserted true.
CNF simplify(CNF formula, int var) {
    for(int i = 0; i < formula.num_clauses; i++) {
        for(int j = 0; j < formula.clauses[i].size(); j++) {
            std::vector<int> &clause = formula.clauses[i];
            if(clause[j] == var) { // Always satisfied after assertion (represented by {0})
                clause = {0};
                break;
            } else if(clause[j] == -var) { // Removes the variable since it is always false
                clause.erase(clause.begin() + j);
                j--;
            } // Does nothing if it can't find the relevant variable
        }
    }

    return formula;
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
CNF unitPropagation(CNF formula, std::unordered_map<int,int> &assignments, bool &exit, bool &changed) {
    while(true) {
        int var = 0;
        bool flag = false;
        for(int i = 0; i < formula.num_clauses; i++) {
            // Empty clause -> Automatically fails
            if(formula.clauses[i].empty()) {
                exit = false;
                return formula;
            }
            
            // Unit clause -> Automatically assigned to satisfy equation
            if(formula.clauses[i].size() == 1) {
                var = formula.clauses[i][0];

                // Checks to see if the unit clause is NOT {0} (aka already satisfied)
                if(var != 0){
                    assignments.insert({std::abs(var), var > 0});
                    flag = true;
                    break;
                }
            }
        }

        // Breaks loop if no more unit clauses are found
        if(!flag) break;

        formula = simplify(formula, var);
        changed = true;
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
CNF pureLiteralElimination(CNF formula, std::unordered_map<int,int> &assignments, int &guess, bool &changed) {
    std::vector<int> count;
    for(int i = 0; i < formula.num_clauses; i++) {
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
            guess = var;
            var = 0;
            count[std::distance(count.begin(), check)] = 0;
        } else {                                            // If no negative polarity is found, sets the corresponding variable to positive.
            assignments.insert({std::abs(var), var > 0});
            formula = simplify(formula, var);
            changed = true;
        }
    }

    return formula;
}

// Runs DPLL algorithm with the satisifiability of the formula being stored in verdict.
// Output is an unordred map of variables to values. (Works similarly to a Python dictionary)
// 0 represents negative, 1 represents positive
std::unordered_map<int,int> DPLL(CNF formula, bool &verdict) {
    // Initialize unordered map and temp CNF (to not modify the original)
    std::unordered_map<int,int> assignments;

    // Repeats unit propagation and pure literal elimination until neither change something.
    // Because both needs to be ran at least once before repeating, one iteration is done outside.
    bool changed = false;
    bool exit = false;
    int guess = 0;

    formula = unitPropagation(formula, assignments, exit, changed);
    if(exit) {
        verdict = false;
        return assignments;
    }
    formula = pureLiteralElimination(formula, assignments, guess, changed);

    while(true){
        if(!changed) break;
        changed = false;

        formula = unitPropagation(formula, assignments, exit, changed);
        if(exit) {
            verdict = false;
            return assignments;
        }

        if(!changed) break;
        changed = false;

        formula = pureLiteralElimination(formula, assignments, guess, changed);
    }

    // Base Cases: Checks to see if all clauses are satisfied or one clause is empty
    bool complete = true;
    for(int i = 0; i < formula.num_clauses; i++) {
        std::vector<int> clause = formula.clauses[i];

        // If a clause is empty, then the code automatically flags this branch as impossible.
        if(clause.size() == 0) {
            verdict = false;
            return assignments;
        }

        // If the complete flag is on and any clause is not specifically {0} (aka satisfied), then the complete flag is turned off.
        if(complete && (clause.size() != 1 || clause[0] != 0)) complete = false;
    }

    if(complete) {
        verdict = true;
        return assignments;
    }

    // Recursion: Selects the first unassigned literal, then tries simplifying with both positive and negative inputs.
    for(int g : {guess, -guess}) {
        bool v = false;
        std::unordered_map<int,int> a = DPLL(simplify(formula, g), v);
        if(v) {
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
        // Skip empty lines
        if (line.empty()) continue;

        std::istringstream iss(line);
        char type;
        iss >> type;

        // Skip comment lines
        if (type == 'c') {
            continue;
        }
        // Problem line: p cnf [num_vars] [num_clauses]
        else if (type == 'p') {
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

    return formula;
}

/*
 * Mode 1: uf20-91: 20 variables, all satisfiable. 1000 files. Filename format: uf20-0X.cnf, where X is the file number.
 * Mode 2: uf50-218: 50 variables, all satisfiable. 1000 files. Filename format: uf50-0X.cnf, where X is the file number.
 * Mode 3: uuf50-218: 50 variables, all unsatisfiable. 1000 files. Filename format: uuf50-0X.cnf, where X is the file number.
 */

const int MODE = 3;

// Command for generating dpll.exe: g++ -o dpll DPLL.cpp
// Command for running program: ./dpll "[X]", where X is the name of the file location of the dataset.
int main(int argc, char* argv[]) {

    if(argc == 1) {
        std::cout << "ERROR: File location not provided." << std::endl;
        return 1;
    } else {
        std::cout << "File location " << argv[1] << " used." << std::endl;
    }

    // Generate the header and file count based on the mode
    std::string folderName;
    std::string fileHeader;
    int fileCount;
    switch(MODE) {
        case 1: 
            folderName = "uf20-91";
            fileHeader = "uf20-0";
            fileCount = 1000;
            break;
        case 2:
            folderName = "uf50-218";
            fileHeader = "uf50-0";
            fileCount = 1000;
            break;
        case 3:
            folderName = "uuf50-218";
            fileHeader = "uuf50-0";
            fileCount = 1000;
            break;

        default:
            break;
    }

    std::string base = argv[1]; // Gets upset if argv[1] is directly plugged into the line below, likely because argv[1] is not a string but a pointer.
    base = base + "\\" + folderName + "\\" + fileHeader;

    std::chrono::time_point<std::chrono::high_resolution_clock> start, end;
    for(int i = 0; i < fileCount; i++) {
        CNF formula = parseFile(base + std::to_string(i + 1) + ".cnf");
        std::cout << "Parsed file " << (i + 1) << ": Has " << formula.num_variables << " variables and " << formula.clauses.size() << " clauses." << std::endl;

        start = std::chrono::high_resolution_clock::now();

        bool verdict = false;
        std::unordered_map<int,int> assignments = DPLL(formula, verdict);

        end = std::chrono::high_resolution_clock::now();

        double duration = (std::chrono::duration_cast<std::chrono::microseconds>(end - start).count()) / 1000.0;

        std::cout << "Verdict: " << verdict << std::endl;
        std::cout << "Duration: " << duration << "ms" << std::endl;
    }
              
    return 0;
}
