#pragma once

#include "mz_terms_all.hpp"

#include <map>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <string>
#include <memory>
#include <algorithm>

#include <minizinc/ast.hh>

using namespace MiniZinc;

// Forward declarations
class Compiler;
class CompilerState;

class CompilerStateLocal {
private:
    std::vector<std::string> _local_var_names;
    bool _in_target_constraint;
    CompilerStateLocal(
        std::vector<std::string> local_var_names,
        bool in_target_constraint
    ) : _local_var_names(local_var_names), _in_target_constraint(in_target_constraint) {
    }
public:
    friend class CompilerState;
};


class CompilerState {
private:
    Compiler* _compiler;
    std::vector<std::string> _global_var_names;                                                 // only modified in Compiler class. for every global declared var, one entry is added
    std::vector<std::string> _local_var_names;                                                  // covers local scope (forall/exists, comprehension, let). stack based in recursion of expression evaluator. can contain duplicates.
    bool _in_target_constraint;
    std::map<Expression*, std::shared_ptr<MzTerm>> _parsed_expressions;
    std::vector<FunctionI*> _function_stack;

public:
    CompilerState(Compiler* compiler);

    void add_global_var_decl(std::shared_ptr<MzVarDecl> var_decl);
    void ensure_id_present(Id* id);
    void add_global_var_name(std::string var_name);
    void add_local_var_name(std::string var_name);
    const std::vector<std::string> local_var_names();
    void set_local_var_names(std::vector<std::string> local_var_names);
    void remove_last_local_var_name();
    bool has_var_name(std::string var_name);
    bool has_global_var_name(std::string var_name);
    bool has_local_var_name(std::string var_name);
    bool in_target_constraint() const;
    void set_in_target_constraint(bool in_target_constraint);

    bool has_parsed_expression(Expression* e);
    void add_parsed_expression(Expression* e, std::shared_ptr<MzTerm> parsed_expression);
    std::shared_ptr<MzTerm> get_parsed_expression(Expression* e);

    CompilerStateLocal reset_local_state();
    void restore_local_state(CompilerStateLocal local_state);
};


// Identifier constructor implementation (needs CompilerState)
inline Identifier::Identifier(CompilerState& compiler_state, std::string mzn_identifier) : _mzn_identifier(mzn_identifier) {
    // TODO calculate prepend_model_name
    _prepend_model_name = !compiler_state.has_local_var_name(mzn_identifier);
    _raw = false;
}


// CompilerState implementations that don't need full Compiler definition
inline CompilerState::CompilerState(Compiler* compiler) : _compiler(compiler), _in_target_constraint(false) {
}

inline CompilerStateLocal CompilerState::reset_local_state() {
    CompilerStateLocal local_state(_local_var_names, _in_target_constraint);
    _local_var_names.clear();
    _in_target_constraint = false;
    return local_state;
}

inline void CompilerState::restore_local_state(CompilerStateLocal local_state) {
    _local_var_names = local_state._local_var_names;
    _in_target_constraint = local_state._in_target_constraint;
}

inline void CompilerState::add_global_var_name(std::string var_name) {
    _global_var_names.push_back(var_name);
}

inline void CompilerState::add_local_var_name(std::string var_name) {
    _local_var_names.push_back(var_name);
}

inline const std::vector<std::string> CompilerState::local_var_names() {
    return _local_var_names;
}

inline void CompilerState::set_local_var_names(std::vector<std::string> local_var_names) {
    _local_var_names = local_var_names;
}

inline void CompilerState::remove_last_local_var_name() {
    _local_var_names.pop_back();
}

inline bool CompilerState::has_var_name(std::string var_name) {
    return std::find(_global_var_names.begin(), _global_var_names.end(), var_name) != _global_var_names.end() ||
           std::find(_local_var_names.begin(), _local_var_names.end(), var_name) != _local_var_names.end();
}

inline bool CompilerState::has_global_var_name(std::string var_name) {
    return std::find(_global_var_names.begin(), _global_var_names.end(), var_name) != _global_var_names.end();
}

inline bool CompilerState::has_local_var_name(std::string var_name) {
    return std::find(_local_var_names.begin(), _local_var_names.end(), var_name) != _local_var_names.end();
}

inline bool CompilerState::in_target_constraint() const {
    return _in_target_constraint;
}

inline void CompilerState::set_in_target_constraint(bool in_target_constraint) {
    _in_target_constraint = in_target_constraint;
}

inline void CompilerState::add_parsed_expression(Expression* e, std::shared_ptr<MzTerm> parsed_expression) {
    _parsed_expressions[e] = parsed_expression;
}

inline std::shared_ptr<MzTerm> CompilerState::get_parsed_expression(Expression* e) {
    return _parsed_expressions[e];
}

inline bool CompilerState::has_parsed_expression(Expression* e) {
    return _parsed_expressions.find(e) != _parsed_expressions.end();
}
