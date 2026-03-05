#pragma once

#include <string>
#include <unordered_map>
#include <iostream>

// Type alias
using lli = long long int;

// Iteration variable prefix
inline std::string it_var = "_i";

// Subscript conversion utility
inline std::string to_subscript(int number) {
    std::string prefix = "";
    if (number < 0) {
        prefix = "\u208B";  // Unicode subscript minus (U+208B)
        number = -number;
    }

    std::string numStr = std::to_string(number);

    static const std::unordered_map<char, std::string> subscriptMap = {
        {'0', "\u2080"},  // U+2080
        {'1', "\u2081"},  // U+2081
        {'2', "\u2082"},  // U+2082
        {'3', "\u2083"},  // U+2083
        {'4', "\u2084"},  // U+2084
        {'5', "\u2085"},  // U+2085
        {'6', "\u2086"},  // U+2086
        {'7', "\u2087"},  // U+2087
        {'8', "\u2088"},  // U+2088
        {'9', "\u2089"}   // U+2089
    };

    std::string result = prefix;
    for (char digit : numStr) {
        result += subscriptMap.at(digit);
    }

    return result;
}


// Function name conversion
inline std::string make_function_lean_name(const std::string& identifier) {
    std::string s = "fun_" + identifier;
    // Replace '\' with '_'
    for (size_t pos = 0; (pos = s.find('\\', pos)) != std::string::npos; pos++) {
        s.replace(pos, 1, "_");
    }
    // Replace '@' with '__'
    for (size_t pos = 0; (pos = s.find('@', pos)) != std::string::npos; pos++) {
        s.replace(pos, 1, "__");
    }
    return s;
}

// Model variable name
inline const std::string MODEL_VAR_NAME = "m" + to_subscript(0);

// Lean helper function names
inline const std::string LEAN_UNTOP_D = "getD";
inline const std::string LEAN_UNBOT_D = "getD";

inline const bool LEAN_SAFE_CHECK_MATH = true;
inline const bool LEAN_SAFE_CHECK_MINMAX = true;

inline const bool LEAN_SAFE_CHECK_ENABLED = true;

// Type annotation config
#define ANNOTATE_TYPES 0
inline const std::string TAO = ANNOTATE_TYPES ? "(" : "";
inline const std::string TAC = ANNOTATE_TYPES ? ")" : "";

// Error handling
[[noreturn]] inline void die(std::string message) {
    std::cerr << message << std::endl;
    exit(1);
}
