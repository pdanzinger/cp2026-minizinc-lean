#pragma once

#include "mz_term_base.hpp"
#include "config.hpp"
#include "utils.hpp"

#include <memory>
#include <vector>
#include <string>
#include <sstream>


// Forward declare Identifier since it depends on CompilerState
class CompilerState;

class Identifier {
private:
    std::string _mzn_identifier;
    bool _prepend_model_name;
    bool _raw;

    Identifier(std::string raw_identifier) : _mzn_identifier(raw_identifier) {
        _prepend_model_name = false;
        _raw = true;
    }
public:
    Identifier(CompilerState& compiler_state, std::string mzn_identifier);

    static Identifier raw(std::string raw_identifier) {
        return Identifier(raw_identifier);
    }

    std::string leanName(bool in_constraint = true) const {
        if (_raw) {
            return _mzn_identifier;
        }

        std::ostringstream os;
        os << ((in_constraint && _prepend_model_name) ? MODEL_VAR_NAME + "." : "") << "var_" << _mzn_identifier;
        return os.str();
    }

    std::string raw_name() const {
        return _mzn_identifier;
    }

    bool operator==(const Identifier& other) const {
        return this->leanName() == other.leanName();
    }

    bool operator!=(const Identifier& other) const {
        return !(*this == other);
    }
};


class MzSetMembership : public MzTerm {
private:
    std::shared_ptr<MzTerm> _set;
    std::shared_ptr<MzTerm> _member;
public:
    MzSetMembership(std::shared_ptr<MzTerm> member, std::shared_ptr<MzTerm> set) : MzTerm(MzType::bool_type(), false), _set(set), _member(member) {
        if (!set->mz_type().is_set() || set->mz_type().inner_type() != member->mz_type()) {
            die("Illegal type. Set membership of non-set or non-matching type.");
        }
    }
    std::string _lean_expr() const override {
        return _member->lean_expr() + " \u2208 " + _set->lean_expr();
    }

    std::string safe_expr() const override {
        return prop_and_default_true(_member->safe_expr(), _set->safe_expr());
    }
};



class MzVarDecl : public MzTerm {
private:
    Identifier _identifier;
    std::shared_ptr<MzTerm> domain;
    std::shared_ptr<MzTerm> definition;
    std::vector<std::shared_ptr<MzTerm>> ranges;
    bool is_array;
    bool is_set;
public:
    MzVarDecl(
        Identifier identifier,
        MzType mzType,
        std::shared_ptr<MzTerm> domain,
        std::shared_ptr<MzTerm> definition,
        std::vector<std::shared_ptr<MzTerm>> ranges
    ) : MzTerm(mzType, false), _identifier(identifier), domain(domain), definition(definition), ranges(ranges) {
        if (mzType.is_array() ? mzType.inner_type().is_opt() : mzType.is_opt()) {
            die("Unsupported: opt types");
        }
        is_array = mzType.is_array();
        is_set = is_array ? mzType.inner_type().is_set() : mzType.is_set();

        // validate definition type
        if (definition != nullptr) {
            if (definition->mz_type() != mzType) {
                die("Illegal definition. Var decl scalar of non-scalar.");
            }
        }

        // validate domain type
        if (domain != nullptr) {
            if (!domain->mz_type().is_set()) {
                die("Illegal domain. Must be a set.");
            }
            if (domain->mz_type().base_type() != mzType.base_type()) {
                die("Illegal domain. Must have the same base type.");
            }
        }
    }

    std::string lean_expr() const override {
        return _identifier.leanName(false) + " : " + mz_type().lean_name();
    }

    std::string domain_expr() {
        std::string expr = "";

        if (is_array) {
            for (size_t i = 0; i < ranges.size(); i++) {
                if (ranges[i] != nullptr) {
                    if (expr != "") {
                        expr += " \u2227 "; // \and;
                    }
                    expr += "(" + _identifier.leanName() + ".dom" + std::to_string(i) + " = " + ranges[i]->lean_expr() + ")";
                }
            }
        }
        if (domain != nullptr) {
            if (expr != "") {
                expr += " \u2227 "; // \and;
            }
            expr += "(";
            if (is_array) {
                std::vector<std::string> var_names;
                for (int i = 0; i < mz_type().array_dims(); i++) {
                    expr += "\u2200"; // \forall;
                    var_names.push_back(make_unique_varname());
                    expr += " " + var_names[i] + " \u2208 " + _identifier.leanName() + ".dom" + std::to_string(i) + ",";
                }
                expr += " (" + _identifier.leanName() + ".toFun";
                for (int i = 0; i < mz_type().array_dims(); i++) {
                    expr += " " + var_names[i];
                }
                expr += ") ";
            } else {
                expr += _identifier.leanName() + " ";
            }

            if (is_set) {
                expr += "\u2286 "; // \subseteq;
                expr += domain->lean_expr();
            } else {
                expr += "\u2208 "; // \in;
                expr += domain->lean_expr();
            }
            expr += ")";
        }
        if (definition != nullptr) {
            if (expr != "") {
                expr += " \u2227 "; // \and;
            }
            expr += _identifier.leanName() + " = " + definition->lean_expr();
        }
        if (expr == "") {
            expr = "True";
        }
        return expr;
    }

    std::shared_ptr<MzTerm> get_domain() const {
        return domain;
    }

    std::shared_ptr<MzTerm> get_definition() const {
        return definition;
    }

    Identifier get_identifier() const {
        return _identifier;
    }

    std::string definition_admissibility_expr() const {
        if (definition == nullptr) {
            return "";
        }

        std::string expr = "";

        if (is_array) {
            for (size_t i = 0; i < ranges.size(); i++) {
                if (ranges[i] != nullptr) {
                    expr = prop_and_default_true(
                        expr,
                        "(" + definition->array_range_expr_at(static_cast<int>(i)) + " = " + ranges[i]->lean_expr() + ")"
                    );
                }
            }
        }

        if (domain != nullptr) {
            std::string domain_check = "(";
            if (is_array) {
                std::vector<std::string> var_names;
                for (int i = 0; i < mz_type().array_dims(); i++) {
                    var_names.push_back(make_unique_varname());
                    domain_check += "\u2200 " + var_names.back() + " \u2208 " + definition->array_range_expr_at(i) + ",";
                }
                domain_check += " " + definition->array_element_at(var_names) + " ";
            } else {
                domain_check += definition->lean_expr() + " ";
            }

            if (is_set) {
                domain_check += "\u2286 " + domain->lean_expr();
            } else {
                domain_check += "\u2208 " + domain->lean_expr();
            }
            domain_check += ")";
            expr = prop_and_default_true(expr, domain_check);
        }

        return expr;
    }

    std::string array_range_expr_at(int dimension) const override {
        if (!mz_type().is_array()) {
            die("MzArrayLike: type must be an array type");
        }
        if (ranges[dimension] != nullptr) {
            return ranges[dimension]->lean_expr();
        }
        return "(" + _identifier.leanName() + ".dom" + std::to_string(dimension) + ")";
    }

    std::string array_element_at(const std::vector<std::shared_ptr<MzTerm>>& indices) const override {
        if (!mz_type().is_array()) {
            die("MzArrayLike: type must be an array type");
        }
        std::string out = "(" + _identifier.leanName() + ".toFun ";

        for (size_t i = 0; i < indices.size(); i++) {
            out += indices[i]->lean_expr() + " ";
        }
        out += ")";

        return out;
    }

    std::string safe_expr() const override {
        std::string expr = "";
        for (const auto& range : ranges) {
            if (range != nullptr) {
                expr = prop_and_default_true(expr, range->safe_expr());
            }
        }
        if (domain != nullptr) {
            expr = prop_and_default_true(expr, domain->safe_expr());
        }
        if (definition != nullptr) {
            expr = prop_and_default_true(expr, definition->safe_expr());
        }
        return expr;
    }
};


class MzId : public MzTerm {
private:
    Identifier _identifier;
    std::shared_ptr<MzVarDecl> _var_decl;
public:
    MzId(Identifier identifier, std::shared_ptr<MzVarDecl> var_decl) : MzTerm(var_decl->mz_type(), true), _identifier(identifier), _var_decl(var_decl) {
    };

    std::string _lean_expr() const override {
        return _identifier.leanName();
    };

    std::string safe_expr() const override {
        return "";
    }

    std::string array_range_expr_at(int dimension) const override {
        return _var_decl->array_range_expr_at(dimension);
    }

    std::string array_element_at(const std::vector<std::shared_ptr<MzTerm>>& indices) const override {
        return _var_decl->array_element_at(indices);
    }
};


class MzITE : public MzTerm {
private:
    std::vector<std::shared_ptr<MzTerm>> _conditions;
    std::vector<std::shared_ptr<MzTerm>> _then_exprs;
    std::shared_ptr<MzTerm> _else_expr;
public:
    MzITE(std::vector<std::shared_ptr<MzTerm>> conditions, std::vector<std::shared_ptr<MzTerm>> then_exprs, std::shared_ptr<MzTerm> else_expr) : MzTerm(then_exprs[0]->mz_type(), false), _conditions(conditions), _then_exprs(then_exprs), _else_expr(else_expr) {
        for (size_t i = 0; i < conditions.size(); i++) {
            if (conditions[i]->mz_type() != MzType::bool_type()) {
                die("MzITE: condition must be bool");
            }
            if (then_exprs[i]->mz_type() != else_expr->mz_type()) {
                die("MzITE: then and else must have the same type");
            }
        }
    }
    std::string _lean_expr() const override {
        std::string expr = "";
        expr += "if " + _conditions[0]->lean_expr() + " then " + _then_exprs[0]->lean_expr();
        for (size_t i = 1; i < _conditions.size(); i++) {
            expr += " else if " + _conditions[i]->lean_expr() + " then " + _then_exprs[i]->lean_expr();
        }
        expr += " else " + _else_expr->lean_expr();
        return expr;
    }

    std::string safe_expr() const override {
        std::string expr = "";
        for (const auto& condition : _conditions) {
            expr = prop_and_default_true(expr, condition->safe_expr());
        }
        for (const auto& then_expr : _then_exprs) {
            expr = prop_and_default_true(expr, then_expr->safe_expr());
        }
        expr = prop_and_default_true(expr, _else_expr->safe_expr());
        return expr;
    }
};


class MzLetIn : public MzTerm {
private:
    std::vector<std::shared_ptr<MzVarDecl>> _var_decls;
    std::vector<std::shared_ptr<Identifier>> _orig_identifiers;
    std::shared_ptr<MzTerm> _body;
public:
    MzLetIn(std::vector<std::shared_ptr<MzVarDecl>> var_decls, std::vector<std::shared_ptr<Identifier>> orig_identifiers, std::shared_ptr<MzTerm> body) : MzTerm(body->mz_type(), false), _var_decls(var_decls), _orig_identifiers(orig_identifiers), _body(body) {
        for (auto var_decl : var_decls) {
            if (var_decl->get_definition() == nullptr) {
                die("MzLetIn: var decl must have a definition");
            }
        }
        if (orig_identifiers.size() != var_decls.size()) {
            die("Var decls and orig_identifiers size must match");
        }
    }
    std::string _lean_expr() const override {
        std::string expr = "";
        for (int i = 0; i < _var_decls.size(); i++) {
            auto& var_decl = _var_decls[i];

            // "orig_identifier" != nullptr <-> "definition existed in model, but not locally"
            // identifiers have both been parsed assuming the name is local, so we need to
            std::shared_ptr<Identifier> orig_identifier = _orig_identifiers[i];
            if (orig_identifier != nullptr) {
                // first in_constraint param doesn't matter here for leanName, since the identifier was constructed as local
                expr += "let " + var_decl->get_identifier().leanName(false) + " = " + orig_identifier->leanName() + "; ";
            }

            if (var_decl->get_definition() != nullptr) {
                expr += "let " + var_decl->lean_expr() + " := " + var_decl->get_definition()->lean_expr() + "; ";
            } else {
                expr += "exists " + var_decl->lean_expr() + ", (" + var_decl->domain_expr() + ") /\\ ";
            }
        }
        expr += _body->lean_expr();
        return expr;
    }

    std::string safe_expr() const override {
        std::string expr = _body->safe_expr();
        for (int i = static_cast<int>(_var_decls.size()) - 1; i >= 0; --i) {
            const auto& var_decl = _var_decls[i];
            std::string decl_safe = var_decl->safe_expr();
            std::string decl_admissibility = var_decl->definition_admissibility_expr();
            if (var_decl->get_definition() != nullptr) {
                if (expr.size() > 0) {
                    expr = "let " + var_decl->lean_expr() + " := " + var_decl->get_definition()->lean_expr() + "; " + expr;
                }
                expr = prop_and_default_true(decl_admissibility, expr);
            } else {
                if (expr.size() > 0) {
                    expr = "\u2200 " + var_decl->lean_expr() + ", " + expr;
                }
            }
            expr = prop_and_default_true(decl_safe, expr);
            std::shared_ptr<Identifier> orig_identifier = _orig_identifiers[i];
            if (orig_identifier != nullptr && expr.size() > 0) {
                expr = "let " + var_decl->get_identifier().leanName(false) + " = " + orig_identifier->leanName() + "; " + expr;
            }
        }
        return expr;
    }
};


class MzSetComprehension : public MzTerm {
private:
    std::shared_ptr<MzTerm> _set;
    Identifier _identifier;
    std::shared_ptr<MzTerm> _expr;
    std::shared_ptr<MzTerm> _where_expr;
public:
    MzSetComprehension(std::shared_ptr<MzTerm> set, Identifier identifier, std::shared_ptr<MzTerm> expr, std::shared_ptr<MzTerm> where_expr) : MzTerm(MzType::set(expr->mz_type().base_type()), false), _set(set), _identifier(identifier), _expr(expr), _where_expr(where_expr) {
        if (!set->mz_type().is_set()) {
            die("Illegal type. Set comprehension of non-set.");
        }
        if (where_expr != nullptr && !where_expr->mz_type().is_bool()) {
            die("Illegal type. Set comprehension of non-bool where expression.");
        }
    }

    std::string _lean_expr() const override {
        std::string expr = "";
        expr += "(";
        expr += _set->lean_expr();
        if (_where_expr != nullptr) {
            expr += ".filter (fun " + _identifier.leanName() + " => " + _where_expr->lean_expr() + ")";
        }
        expr += ")";
        expr += ".image (fun " + _identifier.leanName() + " => " + _expr->lean_expr() + ")";

        return expr;
    }

    std::string safe_expr() const override {
        std::string expr = _set->safe_expr();
        std::string inner = _expr->safe_expr();
        if (_where_expr != nullptr) {
            inner = prop_and_default_true(inner, _where_expr->safe_expr());
        }
        if (inner.size() > 0) {
            inner = "\u2200 " + _identifier.leanName() + " \u2208 " + _set->lean_expr() + ", " + inner;
            expr = prop_and_default_true(expr, inner);
        }
        return expr;
    }
};


/**
 * MiniZinc:
 *   predicate all_different(array [$X] of var $$E: x)
 *   Constrains the elements in the array x to be pairwise different.
 *
 * Lean:
 *   We encode this directly as a Finset-based pairwise distinctness condition:
 *
 *     ∀ i ∈ S, ∀ j ∈ S, i ≠ j → x i ≠ x j
 *
 *   where `S = x.dom0` is the MiniZinc index set (`index_set(x)`).
 *
 * Unicode used:
 *   ∀  (U+2200) = "forall"
 *   ∈  (U+2208) = "membership"
 *   →  (U+2192) = "implies"
 *   ≠  (U+2260) = "not equal"
 */
class MzAllDifferent : public MzTerm {
private:
    std::shared_ptr<MzTerm> _x;
public:
    explicit MzAllDifferent(std::shared_ptr<MzTerm> x) : MzTerm(MzType::bool_type(), false), _x(std::move(x)) {
        if (_x == nullptr) {
            die("MzAllDifferent: missing argument");
        }
        if (!_x->mz_type().is_array() || _x->mz_type().array_dims() != 1) {
            die("MzAllDifferent: expected 1D array argument");
        }
    }

    std::string _lean_expr() const override {
        std::string x_name = make_unique_varname();
        std::string s_name = make_unique_varname();
        std::string i = make_unique_varname();
        std::string j = make_unique_varname();

        auto x_at = [&](const std::string& idx) -> std::string {
            return "(" + x_name + ".toFun " + idx + ")";
        };

        std::ostringstream expr;
        expr << "let " << x_name << " := " << _x->lean_expr() << "; ";
        expr << "let " << s_name << " := " << x_name << ".dom0; ";
        expr << "\u2200 " << i << " \u2208 " << s_name << ", \u2200 " << j << " \u2208 " << s_name << ", "
             << i << " \u2260 " << j << " \u2192 " << x_at(i) << " \u2260 " << x_at(j);
        return expr.str();
    }

    std::string safe_expr() const override {
        return _x->safe_expr();
    }
};


class MzCumulative : public MzTerm {
private:
    std::shared_ptr<MzTerm> _s;
    std::shared_ptr<MzTerm> _d;
    std::shared_ptr<MzTerm> _res;
    std::shared_ptr<MzTerm> _bound;
public:
    MzCumulative(std::shared_ptr<MzTerm> s, std::shared_ptr<MzTerm> d, std::shared_ptr<MzTerm> res, std::shared_ptr<MzTerm> bound) : MzTerm(MzType::bool_type(), false), _s(s), _d(d), _res(res), _bound(bound) {
        if (s->mz_type() != MzType::array(MzType::int_type(), 1)) {
            die("MzCumulative: s must be array of int");
        }
        if (d->mz_type() != MzType::array(MzType::int_type(), 1)) {
            die("MzCumulative: d must be array of int");
        }
        if (res->mz_type() != MzType::array(MzType::int_type(), 1)) {
            die("MzCumulative: res must be array of int");
        }
        if (bound->mz_type() != MzType::int_type()) {
            die("MzCumulative: bound must be int");
        }
    }

    std::string _lean_expr() const override {
        std::string ts = make_unique_varname();
        std::string i = make_unique_varname();
        std::string expr = "";
        std::string s_range_expr = make_unique_varname();
        expr += "let " + s_range_expr + " := " + _s->array_range_expr_at(0) + "; (";
        {
            expr += "(" + s_range_expr + ".card = 0" + ") \u2228 ";
        }
        {
            expr += "(\u2200 " + ts + ", "; // \u2200 = "forall"
            expr += "(";
            {
                std::vector<std::string> indices = {i};
                expr += "\u2211 " + i + " \u2208 " + s_range_expr + ", ";
                expr += "if " + _s->array_element_at(indices) + " <= " + ts + " /\\ " + _s->array_element_at(indices) + " + " + _d->array_element_at(indices) + " > " + ts + " ";
                expr += "then " + _res->array_element_at(indices) + " else 0";
            }
            expr += ")";
            expr += " <= " + _bound->lean_expr();
            expr += ")";
        }
        expr += ")";
        return expr;
    }

    std::string safe_expr() const override {
        std::string expr = _s->safe_expr();
        expr = prop_and_default_true(expr, _d->safe_expr());
        expr = prop_and_default_true(expr, _res->safe_expr());
        expr = prop_and_default_true(expr, _bound->safe_expr());

        std::string s_dom_id = make_unique_varname();
        std::string d_dom_id = make_unique_varname();
        std::string res_dom_id = make_unique_varname();

        std::string arr_content_safety_defs = "";
        arr_content_safety_defs += "let " + s_dom_id + " := " + _s->array_range_expr_at(0) + "; ";
        arr_content_safety_defs += "let " + d_dom_id + " := " + _d->array_range_expr_at(0) + "; ";
        arr_content_safety_defs += "let " + res_dom_id + " := " + _res->array_range_expr_at(0) + "; ";

        std::string arr_content_safety_inner = "";

        arr_content_safety_inner = prop_and_default_true(arr_content_safety_inner, s_dom_id + " = " + d_dom_id);
        arr_content_safety_inner = prop_and_default_true(arr_content_safety_inner, s_dom_id + " = " + res_dom_id);
        // d and r must be nonnegative:
        std::string i = make_unique_varname();
        std::vector<std::string> indices = {i};
        arr_content_safety_inner = prop_and_default_true(arr_content_safety_inner, "\u2200 " + i + " \u2208 " + d_dom_id + ", " + _d->array_element_at(indices) + " >= 0"); // \u2200 = "forall", \u2208 = "membership", \u2192 = "implies", >= = "greater than or equal to"
        arr_content_safety_inner = prop_and_default_true(arr_content_safety_inner, "\u2200 " + i + " \u2208 " + res_dom_id + ", " + _res->array_element_at(indices) + " >= 0"); // \u2200 = "forall", \u2208 = "membership", \u2192 = "implies", >= = "greater than or equal to"
        
        
        expr = prop_and_default_true(expr, arr_content_safety_defs + arr_content_safety_inner);
        return expr;
    }
};


class MzCircuit : public MzTerm {
private:
    std::shared_ptr<MzTerm> _x;
public:
    explicit MzCircuit(std::shared_ptr<MzTerm> x) : MzTerm(MzType::bool_type(), false), _x(std::move(x)) {
        if (_x == nullptr) {
            die("MzCircuit: missing argument");
        }
        if (_x->mz_type() != MzType::array(MzType::int_type(), 1)) {
            die("MzCircuit: x must be array of int (1D)");
        }
    }

    std::string _lean_expr() const override {
        // MiniZinc reference (stdlib/fzn_circuit.mzn):
        //
        //   predicate fzn_circuit(array [int] of var int: x) =
        //     if length(x) = 0 then true else
        //       let {
        //         set of int: S = index_set(x);
        //         int: l = min(S);
        //         int: n = card(S);
        //         array [S] of var 1..n: order;
        //       } in all_different(x) ∧
        //            all_different(order) ∧
        //            forall (i in S) (x[i] != i) ∧
        //            order[l] = 1 ∧
        //            forall (i in S) (order[x[i]] = if order[i] = n then 1 else order[i] + 1 endif)
        //     endif;
        //
        // Lean unicode used below:
        //   ∀  (U+2200) = "forall"
        //   ∈  (U+2208) = "membership"
        //   ∧  (U+2227) = "and"
        //   →  (U+2192) = "implies"
        //   ≠  (U+2260) = "not equal"
        //   ⊆  (U+2286) = "subset of"


        // New Implementation
        std::string S1 = "";
        {
            // New Circuit implementation
            std::string A = make_unique_varname();
            std::string S = make_unique_varname();

            std::string terms = "";

            auto A_at = [&](const std::string& idx) -> std::string {
                return "(" + A + ".toFun " + idx + ")";
            };

            {
                std::string i = make_unique_varname();
                // ∀ i ∈ S, A[i] ∈ S
                terms = prop_and_default_true(terms, "\u2200 " + i + " : Int, " + i + " \u2208 " + S + " \u2192 " + A_at(i) + " \u2208 " + S);
            }

            {
                std::string i = make_unique_varname();
                // ∀ i ∈ S, A[i] ≠ i
                terms = prop_and_default_true(terms, "\u2200 " + i + " : Int, " + i + " \u2208 " + S + " \u2192 " + A_at(i) + " \u2260 " + i);
            }

            {
                std::string i = make_unique_varname();
                std::string j = make_unique_varname();
                // ∀ i ∈ S, ∀ j ∈ S, A[i] = A[j] → i = j
                terms = prop_and_default_true(terms, "\u2200 " + i + " : Int, " + "\u2200 " + j + " : Int, " + i + " \u2208 " + S + " \u2192 " + j + " \u2208 " + S + " \u2192 " + A_at(i) + " = " + A_at(j) + " \u2192 " + i + " = " + j);
            }

            {
                std::string T = make_unique_varname();
                std::string i = make_unique_varname();
                // subtour elimination constraint
                // (∀ T : Finset Int, T ⊆ S → T.Nonempty → T.card < S.card → ∃ i, i ∈ T ∧ A i ∉ T) )
                terms = prop_and_default_true(terms, "\u2200 " + T + " : Finset Int, " + T + " \u2286 " + S + " \u2192 " + T + ".Nonempty \u2192 " + T + ".card < " + S + ".card \u2192 \u2203 " + i + " : Int, " + i + " \u2208 " + T + " \u2227 " + A_at(i) + " \u2209 " + T);
            }

            // Bind A and S and return with the terms
            S1 = "let " + A + " := " + _x->lean_expr() + "; let " + S + " := " + _x->array_range_expr_at(0) + "; " + terms;
            return "let " + A + " := " + _x->lean_expr() + "; let " + S + " := " + _x->array_range_expr_at(0) + "; " + terms;
        }
    }

    std::string safe_expr() const override {
        // No additional safety conditions beyond the argument expression itself:
        // - `min'` is only used in the non-empty branch.
        // - we explicitly enforce `∀ i ∈ S, x[i] ∈ S` in the constraint, so `order[x[i]]` is in-domain.
        return _x->safe_expr();
    }
};
