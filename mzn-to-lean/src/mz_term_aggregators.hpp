#pragma once

#include "mz_term_literals.hpp"
#include "mz_term_misc.hpp"
#include "utils.hpp"

#include <memory>
#include <vector>
#include <sstream>


class MzAggregator : public MzTerm {
public:
    enum class AggregatorType {
        FORALL,
        EXISTS,
        SUM,
        MIN,
        MAX,
    };
private:
    std::shared_ptr<MzTerm> _expr;
    AggregatorType op;
public:

    MzAggregator(std::shared_ptr<MzTerm> expr, AggregatorType op): MzTerm(expr->mz_type().base_type(), false), _expr(expr), op(op) {
        if ((op == AggregatorType::SUM || op == AggregatorType::MIN || op == AggregatorType::MAX) &&
            mz_type() != MzType::int_type() && mz_type() != MzType::float_type()) {
            die("MzAggregator: sum/min/max of unsupported type (expected int or float)");
        }
        if ((op == AggregatorType::FORALL || op == AggregatorType::EXISTS) && mz_type() != MzType::bool_type()) {
            die("MzAggregator: forall/exists of non-bool");
        }
        if (expr->mz_type().is_array()) {
            if (expr->array_dims() == 0) {
                die("MzAggregator: array must have at least one dimension");
            }
        } else {
            if (!expr->mz_type().is_set()) {
                die("MzAggregator: expr result of type array or set expected");
            }
            if (expr->mz_type().base_type() != MzType::int_type()) {
                die("MzAggregator: only sets of int are supported for set mode");
            }
        }
        if (mz_type() == MzType::float_type()) {
            die("MzAggregator: float not supported");
        }
    }
    std::string _lean_expr() const override {
        std::string expr = "";

        if (_expr->mz_type().is_set()) {
            if (op == AggregatorType::SUM) {
                return _expr->lean_expr() + ".sum id";
            }
            if (op == AggregatorType::FORALL) {
                die("MzAggregator: forall of set not supported");
            }
            if (op == AggregatorType::EXISTS) {
                die("MzAggregator: exists of set not supported");
            }
            if (op == AggregatorType::MIN) {
                return _expr->min_expr();
            }
            if (op == AggregatorType::MAX) {
                return _expr->max_expr();
            }
            die("MzAggregator: internal error, unexpected op");
        }

        std::vector<std::string> var_names;
        for (int i = 0; i < _expr->array_dims(); i++) {
            var_names.push_back(make_unique_varname());
        }

        if (op == AggregatorType::MIN || op == AggregatorType::MAX) {

            std::string inner_type_name = (op == AggregatorType::MAX) ? "WithBot" : "WithTop";
            std::string default_name = (op == MzAggregator::AggregatorType::MAX) ? LEAN_UNBOT_D : LEAN_UNTOP_D;
            std::string let_var_name = make_unique_varname();
            expr += "let " + let_var_name + " : " + inner_type_name + " Int := ";
            for (int i = 0; i < _expr->array_dims(); i++) {
                expr += _expr->array_range_expr_at(i) + ".";
                expr += (op == AggregatorType::MAX) ? "sup" : "inf";
                expr += " (";
                expr += "fun " + var_names[i] + " => ";
            }

            expr += "(";
            expr += _expr->array_element_at(var_names);
            expr += " : " + inner_type_name + " Int)";


            for (int i = 0; i < _expr->array_dims(); i++) {
                expr += ")";
            }

            expr += "; " + let_var_name + "." + default_name + " 0";



        } else {
            for (int i = 0; i < _expr->array_dims(); i++) {
                if (op == AggregatorType::SUM) {
                    expr += "\u2211 ";
                } else if (op == AggregatorType::FORALL) {
                    expr += "\u2200 ";
                } else if (op == AggregatorType::EXISTS) {
                    expr += "\u2203 ";
                }
                expr += var_names[i] + " \u2208 " + _expr->array_range_expr_at(i) + ", ";
            }
            expr += _expr->array_element_at(var_names);
        }



        return expr;
    }

    std::string safe_expr() const override {
        std::string expr = _expr->safe_expr();

        if (LEAN_SAFE_CHECK_MINMAX && (op == AggregatorType::MIN || op == AggregatorType::MAX)) {
            if (_expr->mz_type().is_set()) {
                expr = prop_and_default_true(expr, "(0 < (" + _expr->lean_expr() + ").card)");
            } else if (_expr->mz_type().is_array()) {
                for (int i = 0; i < _expr->array_dims(); i++) {
                    std::string dom = _expr->array_range_expr_at(i);
                    expr = prop_and_default_true(expr, "(0 < (" + dom + ").card)");
                }
            }
        }

        return expr;
    }
};

class MzComprehensionAggregator : public MzTerm {
private:
    MzAggregator::AggregatorType op;
    std::vector<std::shared_ptr<MzTerm>> domains;
    std::vector<Identifier> vars;
    std::shared_ptr<MzTerm> _expr;
    std::shared_ptr<MzTerm> _where_expr;
public:

    MzComprehensionAggregator(
        MzAggregator::AggregatorType op,
        std::vector<std::shared_ptr<MzTerm>> domains,
        std::vector<Identifier> vars,
        std::shared_ptr<MzTerm> expr,
        std::shared_ptr<MzTerm> where_expr
    ): MzTerm(expr->mz_type().base_type(), false), _expr(expr), op(op), domains(domains), vars(vars), _where_expr(where_expr) {
        if (domains.size() != vars.size()) {
            die("MzComprehensionAggregator: number of variables must match number of domains");
        }
        for (const auto& domain : domains) {
            if (!domain->mz_type().is_set()) {
                die("MzComprehensionAggregator: all domains must be sets");
            }
        }
        if ((op == MzAggregator::AggregatorType::SUM || op == MzAggregator::AggregatorType::MIN || op == MzAggregator::AggregatorType::MAX) &&
            mz_type() != MzType::int_type() && mz_type() != MzType::float_type()) {
            die("MzComprehensionAggregator: sum/min/max of unsupported type (expected int or float)");
        }
        if ((op == MzAggregator::AggregatorType::FORALL || op == MzAggregator::AggregatorType::EXISTS) && mz_type() != MzType::bool_type()) {
            die("MzComprehensionAggregator: forall/exists of non-bool");
        }
        if (expr->mz_type().is_set()) {
            die("MzComprehensionAggregator: expr result of type set not supported");
        }
        if (mz_type() == MzType::float_type()) {
            die("MzComprehensionAggregator: float not supported");
        }
    }

    std::string _lean_expr() const override {
        std::string expr = "";
        if (op == MzAggregator::AggregatorType::MIN || op == MzAggregator::AggregatorType::MAX) {

            std::string inner_type_name = (op == MzAggregator::AggregatorType::MAX) ? "WithBot" : "WithTop";
            std::string default_name = (op == MzAggregator::AggregatorType::MAX) ? LEAN_UNBOT_D : LEAN_UNTOP_D;
            expr += "(";
            for (size_t i = 0; i < domains.size(); i++) {
                expr += domains[i]->lean_expr() + ".";
                expr += (op == MzAggregator::AggregatorType::MAX) ? "sup" : "inf";
                expr += " (";
                expr += "fun " + vars[i].leanName() + " => ";
            }

            if (_where_expr != nullptr) {
                std::string neutral = (op == MzAggregator::AggregatorType::MAX) ? "\u22A5" : "\u22A4";

                expr += "(if " + _where_expr->lean_expr() + " then ((" + _expr->lean_expr()
                     + ": Int) : " + inner_type_name + " Int) else " + neutral + ")";
            } else {
                expr += "((" + _expr->lean_expr() + ": Int) : " + inner_type_name + " Int)";
            }

            for (size_t i = 0; i < domains.size(); i++) {
                expr += ")";
            }

            expr += ":" + inner_type_name + " Int)." + default_name + " 0";

        }
        if (op == MzAggregator::AggregatorType::SUM || op == MzAggregator::AggregatorType::FORALL || op == MzAggregator::AggregatorType::EXISTS) {
            for (size_t i = 0; i < domains.size(); i++) {
                if (op == MzAggregator::AggregatorType::SUM) {
                    expr += "\u2211 ";
                } else if (op == MzAggregator::AggregatorType::FORALL) {
                    expr += "\u2200 ";
                } else if (op == MzAggregator::AggregatorType::EXISTS) {
                    expr += "\u2203 ";
                }
                expr += vars[i].leanName() + " \u2208 " + domains[i]->lean_expr() + ", ";
            }
            if (_where_expr != nullptr) {
                if (op == MzAggregator::AggregatorType::SUM) {
                    expr += "if " + _where_expr->lean_expr() + " then " + _expr->lean_expr() + " else ";
                    expr += std::make_shared<MzIntLit>(0)->lean_expr();
                } else if (op == MzAggregator::AggregatorType::FORALL) {
                    expr += _where_expr->lean_expr() + " -> " + _expr->lean_expr();
                } else if (op == MzAggregator::AggregatorType::EXISTS) {
                    expr += _where_expr->lean_expr() + " /\\ " + _expr->lean_expr();
                } else {
                    die("MzComprehensionAggregator: internal error, unexpected op");
                }
            } else {
                expr += _expr->lean_expr();
            }
        }
        return expr;
    }

    std::string safe_expr() const override {
        std::string expr = "";
        // Assert that all domains are safe
        for (int i = 0; i < domains.size(); i++) {
            std::string inner_safe_expr = domains[i]->safe_expr();

            if (inner_safe_expr.size() > 0) {
                std::string inner_prefix = "";
                for (int j = 0; j < i; j++) {
                    inner_prefix += "\u2200 " + vars[j].leanName() + " \u2208 " + domains[j]->lean_expr() + ", ";
                }
                expr = prop_and_default_true(expr, inner_prefix + inner_safe_expr);
            }
        }

        // Assert that the inner expression and potentially where conditions are safe
        std::string inner = _expr->safe_expr();
        if (_where_expr != nullptr) {
            inner = prop_and_default_true(inner, _where_expr->safe_expr());
        }
        if (inner.size() > 0) {
            for (int i = static_cast<int>(vars.size()) - 1; i >= 0; --i) {
                inner = "\u2200 " + vars[i].leanName() + " \u2208 " + domains[i]->lean_expr() + ", " + inner; // \u2200 = "forall", \u2208 = "membership"
            }
            expr = prop_and_default_true(expr, inner);
        }

        // For min/max, assert that the domains are non-empty (partiality)
        if (LEAN_SAFE_CHECK_MINMAX && (op == MzAggregator::AggregatorType::MIN || op == MzAggregator::AggregatorType::MAX)) {
            if (_where_expr == nullptr) {
                for (const auto& domain : domains) {
                    expr = prop_and_default_true(expr, "(0 < (" + domain->lean_expr() + ").card)");
                }
            } else {
                // Filtered min/max is only defined when at least one tuple survives the where-clause.
                std::string witness = _where_expr->lean_expr();
                for (int i = static_cast<int>(vars.size()) - 1; i >= 0; --i) {
                    witness = "\u2203 " + vars[i].leanName() + " \u2208 " + domains[i]->lean_expr() + ", " + witness; // \u2203 = "exists", \u2208 = "membership"
                }
                expr = prop_and_default_true(expr, witness);
            }
        }

        return expr;
    }
};
