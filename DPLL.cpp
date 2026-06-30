
// Purpose: Simulate a DPLL algorithm on SATLIB benchmark problems from University of British Columbia

// File parsing
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>

struct CNF {
    int num_variables = 0;
    int num_clauses = 0;
    std::vector<std::vector<int>> clauses;
};

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
 * 
 * 
 */

const int MODE = 1;

int main() {
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

        default:
            break;
    }

    for(int i = 1; i <= fileCount; i++){
        CNF formula = parseFile(folderName + "/" + fileHeader + std::to_string(i) + ".cnf");

        std::cout << "Parsed " << formula.num_variables << " variables and " 
                  << formula.clauses.size() << " clauses." << std::endl;
    }

    return 0;
}