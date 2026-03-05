#pragma once

#include "mz_term_base.hpp"
#include "utils.hpp"

#include <vector>
#include <memory>


class MzIntLit : public MzTerm {
private:
    lli value;
public:
    MzIntLit(lli value) : MzTerm(MzType::int_type(), true), value(value) {
    };
    std::string _lean_expr() const override {
        return std::to_string(value);
    };

    std::string safe_expr() const override {
        return "";
    }

    lli get_value() const {
        return value;
    }
};


class MzBoolLit : public MzTerm {
private:
    bool value;
public:
    MzBoolLit(bool value) : MzTerm(MzType::bool_type(), true), value(value) {
    };
    std::string _lean_expr() const override {
        return value ? "True" : "False";
    };

    std::string safe_expr() const override {
        return "";
    }
};


class MzSetLit : public MzTerm {
    std::vector<std::shared_ptr<MzTerm>> elements;
    MzType base_type;
public:
    MzSetLit(std::vector<std::shared_ptr<MzTerm>> elements, MzType base_type) : MzTerm(MzType::set(base_type), true), elements(elements), base_type(base_type) {
        if (!base_type.is_scalar()) {
            die("Illegal type. Set of non-scalar.");
        }
        if (base_type.is_opt()) {
            die("Illegal type. Set of opt.");
        }
        for (const auto& element : elements) {
            if (element->mz_type() != base_type) {
                die("Illegal type. Set of elements not matching base type.");
            }
        }
    }
    std::string _lean_expr() const override {
        std::string set_expr = "{";
        for (size_t i = 0; i < elements.size(); i++) {
            set_expr += elements[i]->lean_expr() + (i < elements.size() - 1 ? ", " : "");
        }
        set_expr += "}";

        return "(" + set_expr + " : Finset " + base_type.lean_name() + ")";
    }

    std::string safe_expr() const override {
        std::string expr = "";
        for (const auto& element : elements) {
            expr = prop_and_default_true(expr, element->safe_expr());
        }
        return expr;
    }
};

class MzIntSetRange : public MzTerm {
    std::shared_ptr<MzTerm> _lb, _ub;
public:
    MzIntSetRange(std::shared_ptr<MzTerm> lb, std::shared_ptr<MzTerm> ub) : MzTerm(MzType::set(lb->mz_type()), false), _lb(lb), _ub(ub) {
        if (!(lb->mz_type() == MzType::int_type() && ub->mz_type() == MzType::int_type())) {
            die("Illegal type. Set range of non-int.");
        }
    }
    std::string _lean_expr() const override {
        {
            auto lb_int_lit = std::dynamic_pointer_cast<MzIntLit>(_lb);
            auto ub_int_lit = std::dynamic_pointer_cast<MzIntLit>(_ub);
            if (lb_int_lit && ub_int_lit && lb_int_lit->get_value() <= ub_int_lit->get_value()) {
                return "Finset.Icc " + _lb->lean_expr() + " " + _ub->lean_expr();
            }
        }
        return "Finset.Icc " + _lb->lean_expr() + " " + _ub->lean_expr();
    }

    std::string safe_expr() const override {
        return prop_and_default_true(_lb->safe_expr(), _ub->safe_expr());
    }

    std::string min_expr() override {
        return _lb->lean_expr();
    }

    std::string max_expr() override {
        return _ub->lean_expr();
    }

    bool is_nonempty_set() const override {
        {
            auto lb_int_lit = std::dynamic_pointer_cast<MzIntLit>(_lb);
            auto ub_int_lit = std::dynamic_pointer_cast<MzIntLit>(_ub);
            if (lb_int_lit && ub_int_lit && lb_int_lit->get_value() <= ub_int_lit->get_value()) {
                return true;
            }
        }
        return false;
    }
};
