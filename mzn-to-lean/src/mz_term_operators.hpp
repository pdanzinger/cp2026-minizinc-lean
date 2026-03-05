#pragma once

#include "mz_term_base.hpp"

#include <map>
#include <memory>

#include <minizinc/ast.hh>

#include "utils.hpp"

using namespace MiniZinc;


class MzBinOpCmp : public MzTerm {
private:
    std::shared_ptr<MzTerm> lhs, rhs;
    BinOpType op;

    // Generate manual Prop comparison using the same ordering (false < true)
    std::string prop_comparison(const std::string& l, const std::string& r) const {
        switch (op) {
            case BOT_LE: return "\u00AC" + l + " \u2227 " + r;         // false < true
            case BOT_LQ: return "\u00AC" + l + " \u2228 " + r;         // false <= true
            case BOT_GR: return l + " \u2227 \u00AC" + r;              // true > false
            case BOT_GQ: return l + " \u2228 \u00AC" + r;              // true >= false
            case BOT_EQ: return l + " \u2194 " + r;             // equality
            case BOT_NQ: return "\u00AC(" + l + " \u2194 " + r + ")";  // logical XOR
            default: die("Unknown comparison operator"); return "";
        }
    }

public:
    inline static const std::map<BinOpType, std::string> binOpToLeanSymbol = {
        {BOT_LE,    "<"},
        {BOT_LQ,    "<="},
        {BOT_GR,    ">"},
        {BOT_GQ,    ">="},
        {BOT_EQ,    "="},
        {BOT_NQ,    "\u2260"}
    };

    MzBinOpCmp(std::shared_ptr<MzTerm> lhs, std::shared_ptr<MzTerm> rhs, BinOpType op)
        : MzTerm(MzType::bool_type(), false), lhs(lhs), rhs(rhs), op(op) {
        if (!lhs->mz_type().is_scalar() || !rhs->mz_type().is_scalar()) {
            if (op != BOT_EQ && op != BOT_NQ) {
                die("Illegal type. Comparison of non-scalar.");
            }
        }
        if (lhs->mz_type() != rhs->mz_type()) {
            die("Illegal type. Comparison of non-matching types.");
        }
    }

    std::string _lean_expr() const override {
        std::string l = lhs->lean_expr();
        std::string r = rhs->lean_expr();

        if (lhs->mz_type().is_bool()) {
            // Boolean/Prop comparisons - use manual implementation
            return prop_comparison(l, r);
        } else {
            return l + " " + binOpToLeanSymbol.at(op) + " " + r;
        }
    }

    std::string safe_expr() const override {
        return prop_and_default_true(lhs->safe_expr(), rhs->safe_expr());
    }
};

class MzBinOpArith : public MzTerm {
private:
    std::shared_ptr<MzTerm> lhs, rhs;
    BinOpType op;
public:
    inline static const std::map<BinOpType, std::string> binOpToLeanSymbolAscii = {
        // Arithmetic operations
        {BOT_PLUS,  "+"},
        {BOT_MINUS, "-"},
        {BOT_MULT,  "*"},
        {BOT_DIV,   "/"},
        {BOT_IDIV,  "/"},
        {BOT_MOD,   "%"},     // or "mod"
        {BOT_POW,   "^"},
    };

    MzBinOpArith(std::shared_ptr<MzTerm> lhs, std::shared_ptr<MzTerm> rhs, BinOpType op) : MzTerm(lhs->mz_type(), false), lhs(lhs), rhs(rhs), op(op) {
        if (!lhs->mz_type().is_scalar() || !rhs->mz_type().is_scalar()) {
            die("Illegal type. Arithmetic of non-scalar.");
        }
        if (lhs->mz_type() != rhs->mz_type()) {
            die("Illegal type. Arithmetic of non-matching types.");
        }
        if (lhs->mz_type() != MzType::int_type() && lhs->mz_type() != MzType::float_type()) {
            die("Illegal type. Arithmetic of non-numeric type.");
        }
    }
    std::string _lean_expr() const override {
        if (op == BOT_POW && mz_type() == MzType::int_type()) {
            const std::string l_name = make_unique_varname();
            const std::string r_name = make_unique_varname();
            return "(let " + l_name + " := " + lhs->lean_expr() + "; let " + r_name + " := " + rhs->lean_expr() + "; if " + r_name + " >= 0 then " + l_name + " ^ (Int.toNat " + r_name + ") else 1 / (" + l_name + " ^ (Int.toNat (-" + r_name + "))))";
        }
        return lhs->lean_expr() + " " + binOpToLeanSymbolAscii.at(op) + " " + rhs->lean_expr();
    }

    std::string safe_expr() const override {
        std::string expr = prop_and_default_true(lhs->safe_expr(), rhs->safe_expr());

        if (LEAN_SAFE_CHECK_MATH && (op == BOT_DIV || op == BOT_IDIV || op == BOT_MOD)) {
            std::string zero = (mz_type() == MzType::float_type()) ? "0.0" : "0";
            expr = prop_and_default_true(expr, rhs->lean_expr() + " \u2260 " + zero);
        }
        if (LEAN_SAFE_CHECK_MATH && op == BOT_POW && mz_type() == MzType::int_type()) {
            expr = prop_and_default_true(expr, rhs->lean_expr() + " >= 0 \u2228 " + lhs->lean_expr() + " \u2260 0");
        }
        return expr;
    }
};

class MzBinOpBool : public MzTerm {
private:
    std::shared_ptr<MzTerm> lhs, rhs;
    BinOpType op;
public:
    inline static const std::map<BinOpType, std::string> binOpToLeanSymbolAscii = {
        {BOT_EQUIV, "<->"},
        {BOT_IMPL,  "->"},
        {BOT_RIMPL, "->"},
        {BOT_OR,    "\u2228"},
        {BOT_AND,   "\u2227"},
        {BOT_XOR,   "<missing>"},
    };

    MzBinOpBool(std::shared_ptr<MzTerm> lhs, std::shared_ptr<MzTerm> rhs, BinOpType op) : MzTerm(MzType::bool_type(), false), lhs(lhs), rhs(rhs), op(op) {
        if (lhs->mz_type() != MzType::bool_type() || rhs->mz_type() != MzType::bool_type()) {
            die("Illegal type. Logical operation on non-bool.");
        }
    }
    std::string _lean_expr() const override {
        if (op == BOT_RIMPL) {
            // reverse lhs and rhs
            return rhs->lean_expr() + " -> " + lhs->lean_expr();
        }
        if (op == BOT_XOR) {
            return "(" + lhs->lean_expr() + " \u2227 \u00AC" + rhs->lean_expr() + ") \u2228 (\u00AC" + lhs->lean_expr() + " \u2227 " + rhs->lean_expr() + ")";
        }
        return lhs->lean_expr() + " " + binOpToLeanSymbolAscii.at(op) + " " + rhs->lean_expr();
    }

    std::string safe_expr() const override {
        return prop_and_default_true(lhs->safe_expr(), rhs->safe_expr());
    }
};

class MzBinOpSet : public MzTerm {
private:
    std::shared_ptr<MzTerm> _lhs, _rhs;
    BinOpType _op;
public:
    MzBinOpSet(std::shared_ptr<MzTerm> lhs, std::shared_ptr<MzTerm> rhs, BinOpType op)
        : MzTerm(lhs->mz_type(), false), _lhs(std::move(lhs)), _rhs(std::move(rhs)), _op(op) {
        if (!_lhs->mz_type().is_set() || !_rhs->mz_type().is_set()) {
            die("Set binop requires both operands to be sets");
        }
        if (_lhs->mz_type() != _rhs->mz_type()) {
            die("Set binop requires both sets to have the same type");
        }
        if (!(_op == BOT_UNION || _op == BOT_DIFF || _op == BOT_INTERSECT)) {
            die("MzBinOpSet: unsupported operator");
        }
    }

    std::string _lean_expr() const override {
        const std::string l = _lhs->lean_expr();
        const std::string r = _rhs->lean_expr();
        switch (_op) {
            case BOT_UNION:     return l + " \u222A " + r;
            case BOT_INTERSECT: return l + " \u2229 " + r;
            case BOT_DIFF:      return l + " \\ " + r;   // Finset difference
            default: die("MzBinOpSet: internal error");
        }
        return "";
    }

    std::string safe_expr() const override {
        return prop_and_default_true(_lhs->safe_expr(), _rhs->safe_expr());
    }
};

class MzUnOpInt : public MzTerm {
private:
    std::shared_ptr<MzTerm> _term;
    UnOpType op;
public:
    MzUnOpInt(std::shared_ptr<MzTerm> term, UnOpType op) : MzTerm(MzType::int_type(), false), _term(term), op(op) {
        if (term->mz_type() != MzType::int_type()) {
            die("Illegal type. Unary operation on non-int.");
        }
        if (op != UOT_PLUS && op != UOT_MINUS) {
            die("Illegal operation. Unary operation on non-int.");
        }
    };
    std::string _lean_expr() const override {
        return op == UOT_PLUS ? "+" + _term->lean_expr() : "-" + _term->lean_expr();
    }

    std::string safe_expr() const override {
        return _term->safe_expr();
    }
};

class MzUnOpBool : public MzTerm {
private:
    std::shared_ptr<MzTerm> _term;
    UnOpType op;
public:
    MzUnOpBool(std::shared_ptr<MzTerm> term, UnOpType op) : MzTerm(MzType::bool_type(), false), _term(term), op(op) {
        if (term->mz_type() != MzType::bool_type()) {
            die("Illegal type. Unary operation on non-bool.");
        }
        if (op != UOT_NOT) {
            die("Illegal operation. Unary operation on non-bool.");
        }
    };
    std::string _lean_expr() const override {
        return "\u00AC" + _term->lean_expr();
    }

    std::string safe_expr() const override {
        return _term->safe_expr();
    }
};
