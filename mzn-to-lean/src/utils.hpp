#pragma once

#include "config.hpp"
#include "mz_term_base.hpp"

#include <string>
#include <sstream>
#include <unordered_map>
#include <vector>

#include <minizinc/ast.hh>

using namespace MiniZinc;


// Unique variable name generation
inline std::string make_unique_varname() {
    thread_local int index = 0;
    return "_i" + to_subscript(index++);
}


// Usage:
// ExprBuilder b;
// MzTerm e1 = ...;
// MzTerm e2 = ...;
// b.add(e1);
// b.add(e2);
// std::string val_expr = "... some lean code ..." + b.getv(e1) + "...";
// std::string s_expr = "... some lean code ..." + b.gets(e1) + "...";
// std::string out = b.build(val_expr, s_expr);
// out == "let _i₀ := " + e1.lean_expr() + "; let _i₁ := " + e2.lean_expr() + "; ⟨" + val_expr + ", " + s_expr + "⟩";
// return b.build(val_expr, s_expr);
class ExprBuilder {
private:
    std::vector<std::pair<std::string, std::string>> _bindings;
    std::unordered_map<std::string, std::string> _names;

    std::string _name_of(const MzTerm& term) const {
        auto it = _names.find(term.lean_expr());
        if (it == _names.end()) {
            die("ExprBuilder: term not added");
        }
        return it->second;
    }

public:
    void add(const MzTerm& term) {
        std::string expr = term.lean_expr();
        if (_names.find(expr) != _names.end()) {
            return;
        }
        std::string name = make_unique_varname();
        _bindings.emplace_back(name, expr);
        _names.emplace(expr, name);
    }

    std::string getv(const MzTerm& term) const {
        return "(" + _name_of(term) + ".1)";
    }

    std::string gets(const MzTerm& term) const {
        return "(" + _name_of(term) + ".2)";
    }

    std::string build(const std::string& val_expr, const std::string& s_expr) const {
        std::string out;
        for (const auto& [name, expr] : _bindings) {
            out += "let " + name + " := " + expr + "; ";
        }
        out += "⟨" + val_expr + ", " + s_expr + "⟩";
        return out;
    }
};


// Check and enforce non-optional types
inline void enforce_non_opt(Expression* e) {
    if (Expression::type(e).isOpt()) {
        die("Unsupported Expression: enforce_non_opt");
    }
}

inline std::string normalize_mzn_call_name(std::string call_name) {
    if (auto pos = call_name.find('@'); pos != std::string::npos) {
        call_name.erase(0, pos + 1);
    }
    return call_name;
}

std::string prop_and_default_true(std::string expr1, std::string expr2) {
    if (expr1.size() == 0 || expr2.size() == 0) {
        return expr1 + expr2;
    }
    return "(" + expr1 + " \u2227 " + expr2 + ")";
}
