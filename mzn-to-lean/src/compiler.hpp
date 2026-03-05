#pragma once

#include "expression_parser.hpp"
#include "compiler_state.hpp"
#include "config.hpp"

#include <minizinc/ast.hh>
#include <minizinc/astiterator.hh>
#include <minizinc/model.hh>

#include <iostream>
#include <sstream>
#include <string>
#include <tuple>
#include <vector>

using namespace MiniZinc;


// Forward declarations for get_lean_prefix
std::string get_lean_prefix();

class ConstraintResult {
public:
    const std::string expr;
    const std::string safe_expr;
    const bool has_safe_expr;
    const bool redundant;
    ConstraintResult(std::string expr, std::string safe_expr, bool redundant) : expr(std::move(expr)), safe_expr(std::move(safe_expr)), has_safe_expr(this->safe_expr.size()>0), redundant(redundant) {
    }
};

class Compiler : public ItemVisitor {
protected:
    std::vector<std::string> var_decl_lines;
    std::vector<std::string> func_lines;
    std::vector<ConstraintResult> cons_lines;
    CompilerState _compiler_state;
    std::string _redundant_ann_name;
    std::string _cons_ann_ignore_name;
    bool _prove_non_redundant;
public:
    Compiler(std::string redundant_ann_name, std::string cons_ann_ignore_name, bool prove_non_redundant);
    void vVarDeclI(VarDeclI* vdi);
    void vConstraintI(ConstraintI* ci);
    void vFunctionI(FunctionI*);
    bool enter(Item* i);
    void addGlobalVarDecl(std::shared_ptr<MzVarDecl> var_decl);
    std::string get_full_lean_model();
};

Compiler::Compiler(std::string redundant_ann_name, std::string cons_ann_ignore_name, bool prove_non_redundant) : _compiler_state(this), _redundant_ann_name(redundant_ann_name), _cons_ann_ignore_name(cons_ann_ignore_name), _prove_non_redundant(prove_non_redundant) {
}

// CompilerState implementations that need Compiler
inline void CompilerState::add_global_var_decl(std::shared_ptr<MzVarDecl> var_decl) {
    _compiler->addGlobalVarDecl(var_decl);
}

inline void CompilerState::ensure_id_present(Id* id) {
    if (!id->hasStr()) {
        die("id must have string");
    }
    std::string name(id->v().c_str());
    if (!has_var_name(name)) {
        if (id->decl() == nullptr) {
            die("no declaration present, but var not in scope");
        }
        CompilerStateLocal local_state = reset_local_state();
        _compiler->vVarDeclI(id->decl()->item());
        restore_local_state(local_state);
    }
}




inline void Compiler::addGlobalVarDecl(std::shared_ptr<MzVarDecl> var_decl) {
    std::string var_name = var_decl->get_identifier().raw_name();

    std::string expr = var_decl->lean_expr();
    std::cerr << "" << expr << std::endl;

    var_decl_lines.push_back(expr);

    if (var_decl->domain_expr().size() > 0 && var_decl->domain_expr() != "True") {
        std::string domain_expr = var_decl->domain_expr();
        std::string safe_expr = var_decl->safe_expr();
        std::cerr << "adding cons: " << domain_expr << " with safe expr: " << safe_expr << std::endl;
        cons_lines.push_back(ConstraintResult(domain_expr, safe_expr, false));
    }

    _compiler_state.add_global_var_name(var_name);

}

inline void Compiler::vVarDeclI(VarDeclI* vdi) {
    auto* vd = vdi->e();
    std::string var_name(vdi->e()->id()->v().c_str());

    if (vd->ti()->type().bt() == Type::BT_ANN) {
        std::cerr << "(skipping annotation declaration)" << std::endl;
        return;
    }
    if (_compiler_state.has_global_var_name(var_name)) {
        std::cerr << "(skipping duplicate declaration of " << var_name << ")" << std::endl;
        return;
    }

    MzExpressionParser parser;
    auto result = std::dynamic_pointer_cast<MzVarDecl>(parser.parseExpression(_compiler_state, vd));
    addGlobalVarDecl(result);
}

inline void Compiler::vFunctionI(FunctionI* fi) {
    if (fi == nullptr) {
        die("Compiler::vFunctionI: null function");
    }
    if (fi->e() == nullptr) {
        std::cerr << "Compiler::vFunctionI: function has no body: " << std::string(fi->id().c_str());
        return;
    }
    if (fi->ti() == nullptr) {
        die("Compiler::vFunctionI: function has no return type: " + std::string(fi->id().c_str()));
    }
    
    die("Compiler::vFunctionI: not implemented");
}


inline void Compiler::vConstraintI(ConstraintI* ci) {
    auto* e = ci->e();

    bool redundant = false;

    for (auto ann : Expression::ann(e)) {
        if (Expression::eid(ann) == Expression::E_ID) {
            auto id = ann->cast<Id>(ann);
                std::string ann_name(id->v().c_str());
            if (ann_name == _cons_ann_ignore_name) {
                std::cerr << "ignoring constraint due to " << _cons_ann_ignore_name << std::endl;
                return;
            }
            if (ann_name == _redundant_ann_name) {
                redundant = true;
                break;
            }
        }
    }
    if (Expression::eid(e) == Expression::E_CALL) {
        auto call = Expression::cast<Call>(e);
        std::string call_name = normalize_mzn_call_name(std::string(call->id().c_str()));
        if (call_name == "mzn_redundant_constraint") {
            if (call->argCount() != 1) {
                die("wrong arg count for minizinc_redundant_constraint");
            }
            redundant = true;
            e = call->arg(0);
        }
    }

    MzExpressionParser parser;
    std::cerr << "--constraint at loc " << ci->loc().toString() << std::endl;
    bool old_in_target_constraint = _compiler_state.in_target_constraint();
    _compiler_state.set_in_target_constraint(redundant);
    auto result = parser.parseExpression(_compiler_state, e);
    _compiler_state.set_in_target_constraint(old_in_target_constraint);
    if (result->mz_type() != MzType::bool_type()) {
        die("constraint type must be bool");
    }
    std::string expr = result->lean_expr();
    std::string safe_expr = result->safe_expr();

    if (redundant) std::cerr << "redundant ";
    std::cerr << "cons: " << expr << " with safe expr: " << safe_expr << std::endl;
    cons_lines.push_back(ConstraintResult(expr, safe_expr, redundant));
}


inline bool Compiler::enter(Item* i) {
    if (i->iid() == Item::ItemId::II_INC) {
        return false;
    }
    return true;
}


inline std::string get_lean_prefix() {
    std::string out = "";

    out += R"(
import Mathlib
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat


-- These lines work to assume that every Prop is decidable. I.e. if p : Prop, then (decide p) will always work
open Classical
noncomputable section
classical

)";

if (true)
    out += R"(

-- MiniZinc Array Types. Represents MiniZinc arrays of dimensions 1 through 8 in Lean.
-- The array contents are modelled by toFun, dom0 through domN are the array boundaries. Boundaries for accesses are enforced through safety formulas.

universe u

/-- Helper: product of a list of Nats. -/
def listProd : List Nat → Nat := List.foldl (· * ·) 1

/-- Nonempty contiguous finite integer set. -/
def mzIsContiguousIntSet (s : Finset Int) : Prop :=
    0 < s.card ∧ Int.ofNat s.card = (s.max.getD 0 - s.min.getD 0 + 1)

/-- 1D array with element type α. -/
structure Array1d (α : Type u) where
    dom0  : Finset Int
    toFun : Int → α

/-- 2D array with element type α. -/
structure Array2d (α : Type u) where
    dom0  : Finset Int
    dom1  : Finset Int
    toFun : Int → Int → α

/-- 3D array with element type α. -/
structure Array3d (α : Type u) where
    dom0  : Finset Int
    dom1  : Finset Int
    dom2  : Finset Int
    toFun : Int → Int → Int → α

/-- 4D array with element type α. -/
structure Array4d (α : Type u) where
    dom0  : Finset Int
    dom1  : Finset Int
    dom2  : Finset Int
    dom3  : Finset Int
    toFun : Int → Int → Int → Int → α

/-- 5D array with element type α. -/
structure Array5d (α : Type u) where
    dom0  : Finset Int
    dom1  : Finset Int
    dom2  : Finset Int
    dom3  : Finset Int
    dom4  : Finset Int
    toFun : Int → Int → Int → Int → Int → α

/-- 6D array with element type α. -/
structure Array6d (α : Type u) where
    dom0  : Finset Int
    dom1  : Finset Int
    dom2  : Finset Int
    dom3  : Finset Int
    dom4  : Finset Int
    dom5  : Finset Int
    toFun : Int → Int → Int → Int → Int → Int → α

/-- 7D array with element type α. -/
structure Array7d (α : Type u) where
    dom0  : Finset Int
    dom1  : Finset Int
    dom2  : Finset Int
    dom3  : Finset Int
    dom4  : Finset Int
    dom5  : Finset Int
    dom6  : Finset Int
    toFun : Int → Int → Int → Int → Int → Int → Int → α

/-- 8D array with element type α. -/
structure Array8d (α : Type u) where
    dom0  : Finset Int
    dom1  : Finset Int
    dom2  : Finset Int
    dom3  : Finset Int
    dom4  : Finset Int
    dom5  : Finset Int
    dom6  : Finset Int
    dom7  : Finset Int
    toFun : Int → Int → Int → Int → Int → Int → Int → Int → α

namespace Array1d

/-- MiniZinc `length`: total number of elements in the array. -/
def size (a : Array1d α) : Nat :=
    listProd [a.dom0.card]

end Array1d

namespace Array2d

/-- MiniZinc `length`: total number of elements in the array. -/
def size (a : Array2d α) : Nat :=
    listProd [a.dom0.card, a.dom1.card]

end Array2d

namespace Array3d

/-- MiniZinc `length`: total number of elements in the array. -/
def size (a : Array3d α) : Nat :=
    listProd [a.dom0.card, a.dom1.card, a.dom2.card]

end Array3d

namespace Array4d

/-- MiniZinc `length`: total number of elements in the array. -/
def size (a : Array4d α) : Nat :=
    listProd [a.dom0.card, a.dom1.card, a.dom2.card, a.dom3.card]

end Array4d

namespace Array5d

/-- MiniZinc `length`: total number of elements in the array. -/
def size (a : Array5d α) : Nat :=
    listProd [a.dom0.card, a.dom1.card, a.dom2.card, a.dom3.card, a.dom4.card]

end Array5d

namespace Array6d

/-- MiniZinc `length`: total number of elements in the array. -/
def size (a : Array6d α) : Nat :=
    listProd [a.dom0.card, a.dom1.card, a.dom2.card, a.dom3.card, a.dom4.card, a.dom5.card]

end Array6d

namespace Array7d

/-- MiniZinc `length`: total number of elements in the array. -/
def size (a : Array7d α) : Nat :=
    listProd [a.dom0.card, a.dom1.card, a.dom2.card, a.dom3.card, a.dom4.card, a.dom5.card, a.dom6.card]

end Array7d

namespace Array8d

/-- MiniZinc `length`: total number of elements in the array. -/
def size (a : Array8d α) : Nat :=
    listProd [a.dom0.card, a.dom1.card, a.dom2.card, a.dom3.card, a.dom4.card, a.dom5.card, a.dom6.card, a.dom7.card]

end Array8d

-- Other definitions:

def mz_bool2int (b : Prop) : Int := if b then (1 : Int) else (0 : Int)

-- The compiled MiniZinc model with the constraints to prove:

)";

    return out;
}


inline std::string Compiler::get_full_lean_model() {
    std::ostringstream model;
    model << get_lean_prefix();

    model << "structure Model where" << std::endl;
    for (auto& var_line : var_decl_lines) {
        model << "  " << var_line << std::endl;
    }
    model << std::endl;

    for (auto& func_line : func_lines) {
        model << func_line << std::endl;
    }
    if (!func_lines.empty()) {
        model << std::endl;
    }

    for (int i = 0; i < cons_lines.size(); i++) {
        ConstraintResult& cons_result = cons_lines[i];
        model << "def cons" << to_subscript(i) << " (" << MODEL_VAR_NAME << " : Model) : Prop := " << cons_result.expr << std::endl;
        if (LEAN_SAFE_CHECK_ENABLED && cons_result.has_safe_expr && (cons_result.redundant)) {
            model << "def safe_cons" << to_subscript(i) << " (" << MODEL_VAR_NAME << " : Model) : Prop := " << cons_result.safe_expr << std::endl;
        }
    }
    model << std::endl;

    if (_prove_non_redundant) {
        model << "theorem theorem_redundant : \u2203 " << MODEL_VAR_NAME << ": Model, "; // \exists
        bool first = true;
        for (int i = 0; i < cons_lines.size(); i++) {
            ConstraintResult& cons_result = cons_lines[i];
            if (!cons_result.redundant) {
                if (!first) {
                    model << "\u2227 "; // \and;
                }
                model << "(cons" << to_subscript(i) << " " << MODEL_VAR_NAME << ") ";
                first = false;
            }
        }
        if (!first) {
            model << "\u2227 "; // \and;
        }
        model << "\u00ac "; // \neg;
        model << "(";
        first = true;
        for (int i = 0; i < cons_lines.size(); i++) {
            ConstraintResult& cons_result = cons_lines[i];
            if (cons_result.redundant) {
                if (!first) {
                    model << "\u2227 "; // \and;
                }
                model << "(cons" << to_subscript(i) << " " << MODEL_VAR_NAME << ") ";
                if (LEAN_SAFE_CHECK_ENABLED && cons_result.has_safe_expr) {
                    model << "\u2227 (safe_cons" << to_subscript(i) << " " << MODEL_VAR_NAME << ") ";
                }
                first = false;
            }
        }
        if (first) {
            model << "True";
        }
        model << ") ";
    } else {
        model << "theorem theorem_redundant (" << MODEL_VAR_NAME << ": Model) ";
        for (int i = 0; i < cons_lines.size(); i++) {
            ConstraintResult& cons_result = cons_lines[i];
            if (!cons_result.redundant) {
                model << "(h" << to_subscript(i) << ": cons" << to_subscript(i) << " " << MODEL_VAR_NAME << ") ";
            }
        }
        model << ": ";
        bool first = true;
        for (int i = 0; i < cons_lines.size(); i++) {
            ConstraintResult& cons_result = cons_lines[i];
            if (cons_result.redundant) {
                if (!first) {
                    model << "\u2227 "; // \and;
                }
                model << "(cons" << to_subscript(i) << " " << MODEL_VAR_NAME << ") ";
                if (LEAN_SAFE_CHECK_ENABLED && cons_result.has_safe_expr) {
                    model << "\u2227 (safe_cons" << to_subscript(i) << " " << MODEL_VAR_NAME << ") ";
                }
                first = false;
            }
        }
        if (first) {
            model << "True ";
        }
    }

    model << ":= by";
    model << std::endl;
    model << "  sorry" << std::endl;

    return model.str();

}
