#pragma once

#include "mz_term_base.hpp"
#include "utils.hpp"

#include <memory>
#include <sstream>
#include <functional>


class MzBinFunc : public MzTerm {
public:

    enum class BinFuncType {
        MIN,
        MAX,
    };

private:
    std::shared_ptr<MzTerm> _lhs, _rhs;
    MzBinFunc::BinFuncType func_type;
public:

    MzBinFunc(std::shared_ptr<MzTerm> lhs, std::shared_ptr<MzTerm> rhs, BinFuncType func_type) : MzTerm(lhs->mz_type(), false), _lhs(lhs), _rhs(rhs), func_type(func_type) {
        if (lhs->mz_type() != rhs->mz_type()) {
            die("MzBinFunc: lhs and rhs must have the same type");
        }
        if (!lhs->mz_type().is_scalar()) {
            die("MzBinFunc: lhs and rhs must be scalar");
        }
    }
    std::string _lean_expr() const override {
        std::string lean_function = func_type == BinFuncType::MIN ? "min" : "max";
        return lean_function + " " + _lhs->lean_expr() + " " + _rhs->lean_expr();
    }

    std::string safe_expr() const override {
        return prop_and_default_true(_lhs->safe_expr(), _rhs->safe_expr());
    }
};

class MzUnFunc : public MzTerm {
public:
    enum class UnFuncType {
        BOOL2INT,
    };
private:
    std::shared_ptr<MzTerm> _term;
    UnFuncType func_type;
public:
    MzUnFunc(std::shared_ptr<MzTerm> term, UnFuncType func_type) : MzTerm(func_type == UnFuncType::BOOL2INT ? MzType::int_type() : term->mz_type(), false), _term(term), func_type(func_type) {
};
    std::string _lean_expr() const override {
        if (func_type == UnFuncType::BOOL2INT) {
            return "mz_bool2int " + _term->lean_expr();
        }
        die("MzUnFunc: internal error, unexpected func_type");
    }

    std::string safe_expr() const override {
        return _term->safe_expr();
    }
};
