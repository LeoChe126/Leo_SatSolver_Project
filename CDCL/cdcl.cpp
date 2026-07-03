
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <string>
#include <filesystem>
#include <chrono>
#include <unordered_map>
#include <cmath>
#include <algorithm>
#include <limits>

struct CNF {
    int num_variables = 0;
    int num_clauses = 0;
    std::vector<std::vector<int>> clauses;
    int decision_level = 0; 

};


