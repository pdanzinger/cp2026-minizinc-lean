#pragma once

#include "mz_term_literals.hpp"
#include "mz_term_misc.hpp"
#include "utils.hpp"

#include <memory>
#include <vector>
#include <sstream>


class MzArrayAccess : public MzTerm {
private:
    std::shared_ptr<MzTerm> _array;
    std::vector<std::shared_ptr<MzTerm>> _indices;
public:
    MzArrayAccess(std::shared_ptr<MzTerm> array, std::vector<std::shared_ptr<MzTerm>> indices) : MzTerm(array->mz_type().inner_type(), false), _array(array), _indices(indices) {
        if (!array->mz_type().is_array()) {
            die("Illegal type. Array access of non-array.");
        }
        if (array->mz_type().array_dims() != static_cast<int>(indices.size())) {
            die("Illegal type. Array access of wrong number of indices.");
        }
    }
public:
    std::string _lean_expr() const override {
        return _array->array_element_at(_indices);
    }

    std::string safe_expr() const override {
        std::string expr = _array->safe_expr();
        for (size_t i = 0; i < _indices.size(); i++) {
            expr = prop_and_default_true(expr, _indices[i]->safe_expr());
            std::string dom = "(" + _array->array_range_expr_at(static_cast<int>(i)) + ")";
            expr = prop_and_default_true(expr, _indices[i]->lean_expr() + " \u2208 " + dom);
        }
        return expr;
    }
};

class MzArrayComprehension : public MzTerm {
private:
    std::vector<std::shared_ptr<MzTerm>> domains;
    std::vector<Identifier> vars;
    std::shared_ptr<MzTerm> expr;
    bool collapse_dims;
    std::string _collapsed_dim_width_expr(int i) const {
        return "(" + domains[i]->max_expr() + " - " + domains[i]->min_expr() + " + 1)";
    }
    std::string _collapsed_body_expr(const std::string& linear_index_expr) const {
        std::ostringstream result;
        std::string cur_rem = make_unique_varname();
        result << "(let " << cur_rem << " := " << linear_index_expr << " - 1; ";

        for (int i = static_cast<int>(vars.size()) - 1; i >= 0; --i) {
            std::string next_rem = make_unique_varname();
            result << "let " << vars[i].leanName() << " := " << domains[i]->min_expr()
                   << " + (" << cur_rem << " % " << _collapsed_dim_width_expr(i) << "); ";
            result << "let " << next_rem << " := Int.div " << cur_rem << " " << _collapsed_dim_width_expr(i) << "; ";
            cur_rem = next_rem;
        }
        result << expr->lean_expr() << ")";
        return result.str();
    }
public:
    MzArrayComprehension(
        std::vector<std::shared_ptr<MzTerm>> domains,
        std::vector<Identifier> vars,
        std::shared_ptr<MzTerm> expr,
        bool collapse_dims
    ) : MzTerm(MzType::array(expr->mz_type(), collapse_dims ? 1 : domains.size()), false),
        domains(domains),
        vars(vars),
        expr(expr),
        collapse_dims(collapse_dims)
    {
        if (domains.size() != vars.size()) {
            die("MzArrayComprehension: number of variables must match number of domains");
        }

        for (const auto& domain : domains) {
            if (domain->mz_type() != MzType::set(MzType::int_type())) {
                die("MzArrayComprehension: all domains must be int sets");
            }
        }
    }


    std::string _fun_expr() const {
        std::ostringstream result;
        result << "(";
        if (collapse_dims && vars.size() > 1) {
            std::string linear_index = make_unique_varname();
            result << "fun " << linear_index << " => " << _collapsed_body_expr(linear_index);
        } else {
            result << "fun";

            for (const Identifier& var : vars) {
                result << " " << var.leanName();
            }
            result << " => ";
            result << expr->lean_expr();
        }
        result << ")";

        return result.str();
    }

    std::string _lean_expr() const override {
        std::ostringstream result;
        result << "({toFun := " << _fun_expr();
        for (size_t i = 0; i < (collapse_dims ? 1 : domains.size()); i++) {
            result << ", dom" << i << " := " << array_range_expr_at(i);
        }
        result << "} : " << mz_type().lean_name() << ")";
        return result.str();
    }

    std::string safe_expr() const override {
        std::string expr = "";
        for (const auto& domain : domains) {
            expr = prop_and_default_true(expr, domain->safe_expr());
        }

        std::string inner = this->expr->safe_expr();
        if (inner.size() > 0) {
            for (int i = static_cast<int>(vars.size()) - 1; i >= 0; --i) {
                std::string dom_expr;
                if (collapse_dims && vars.size() > 1) {
                    dom_expr = "Finset.Icc " + domains[i]->min_expr() + " " + domains[i]->max_expr();
                } else {
                    dom_expr = domains[i]->lean_expr();
                }
                inner = "\u2200 " + vars[i].leanName() + " \u2208 " + dom_expr + ", " + inner;
            }
            expr = prop_and_default_true(expr, inner);
        }

        if (collapse_dims && vars.size() > 1) {
            for (const auto& domain : domains) {
                expr = prop_and_default_true(expr, "mzIsContiguousIntSet (" + domain->lean_expr() + ")");
            }
        }

        return expr;
    }

    std::string array_range_expr_at(int dimension) const override {
        if (dimension < 0 || dimension >= static_cast<int>(domains.size())) {
            die("MzArrayComprehension: dimension index out of bounds");
        }
        if (collapse_dims && vars.size() > 1) {
            std::string max_expr_str;
            for (size_t i = 0; i < vars.size(); i++) {
                if (max_expr_str.size() > 0) {
                    max_expr_str += " * ";
                }
                max_expr_str += "(" + domains[i]->max_expr() + " - " + domains[i]->min_expr() + " + 1) ";
            }
            return "(Finset.Icc 1 (" + max_expr_str + "))";
        } else {
            return domains[dimension]->lean_expr();
        }
    }

    std::string array_element_at(const std::vector<std::shared_ptr<MzTerm>>& indices) const override {
        if (collapse_dims && vars.size() > 1) {
            if (indices.size() != 1) {
                die("MzArrayComprehension: collapsed access expects exactly one index");
            }
            return _collapsed_body_expr(indices[0]->lean_expr());
        }
        std::string out = "(";
        for (size_t i = 0; i < indices.size(); i++) {
            out += "let " + vars[i].leanName() + " := " + indices[i]->lean_expr() + "; ";
        }
        out += expr->lean_expr();
        out += ")";
        return out;
    }

    std::string array_element_at(const std::vector<std::string>& indices) const override {
        if (collapse_dims && vars.size() > 1) {
            if (indices.size() != 1) {
                die("MzArrayComprehension: collapsed access expects exactly one index");
            }
            return _collapsed_body_expr(indices[0]);
        }
        std::string out = "(";
        for (size_t i = 0; i < indices.size(); i++) {
            out += "let " + vars[i].leanName() + " := " + indices[i] + "; ";
        }
        out += expr->lean_expr();
        out += ")";
        return out;
    }

    
};


class MzArrayLit : public MzTerm {
private:
    int _dims;
    std::vector<std::pair<int, int>> _ranges;
    std::vector<std::shared_ptr<MzTerm>> _elements;
public:
    MzArrayLit(int dims,
               std::vector<std::pair<int, int>> ranges,
               std::vector<std::shared_ptr<MzTerm>> elements,
               const MzType& elem_type)
        : MzTerm(MzType::array(elem_type, dims), false),
          _dims(dims),
          _ranges(std::move(ranges)),
          _elements(std::move(elements)) {
        if (dims <= 0) {
            die("MzArrayLit: dims must be positive");
        }
        if (dims >= 2) {
            die("MzArrayLit: multi-dimensional arrays are currently not supported");
        }
        if (static_cast<int>(_ranges.size()) != dims) {
            die("MzArrayLit: ranges must have the same length as dims");
        }
        int numel = 1;
        for (auto& range : _ranges) {
            numel *= (range.second - range.first + 1);
            if (range.second < range.first) {
                numel = 0;
            }
        }
        if (static_cast<int>(_elements.size()) != numel) {
            die("MzArrayLit: elements must have the same length as the number of elements in the ranges");
        }
        for (const auto& elem : _elements) {
            if (elem->mz_type() != elem_type) {
                die("MzArrayLit: element type mismatch");
            }
        }
    }

    std::string _fun_expr() const {
        const int d = _dims;
        const int size = _ranges[0].second - _ranges[0].first + 1;
        auto default_value_expr = [&]() -> std::string {
            const MzType t = mz_type().inner_type();
            if (t == MzType::int_type()) return "0";
            if (t == MzType::float_type()) return "0.0";
            if (t == MzType::bool_type()) return "False";
            if (t.is_set()) return "\u2205";
            die("MzArrayLit: unsupported element type");
            return "0";
        };

        std::string default_value = _elements.empty() ? default_value_expr() : _elements[0]->lean_expr();
        std::string elem_type = mz_type().inner_type().lean_name();
        std::string temp_var_name = make_unique_varname();

        if (size <= 10) {
            std::ostringstream fun;
            fun << "(fun (" << temp_var_name << " : Int) => match " << temp_var_name << " with ";
            int start = _ranges[0].first;
            for (int i = 0; i < size; ++i) {
                fun << " | (" << (start + i) << " : Int) => " << _elements[i]->lean_expr();
            }
            fun << " | _ => " << default_value << ")";
            return fun.str();
        }

        std::string var = make_unique_varname();


        std::ostringstream data;
        data << "let __data : Array " << elem_type << " := #[";
        for (size_t i = 0; i < _elements.size(); ++i) {
            if (i > 0) data << ", ";
            data << _elements[i]->lean_expr();
        }
        data << "]; ";

        std::string idx = "(" + var + " - " + std::to_string(_ranges[0].first) + ")";

        std::ostringstream fun;
        fun << "(fun";
        fun << " " << var;
        fun << " => ";
        fun << data.str();
        fun << "Option.getD (__data.get? (Int.toNat " << idx << ")) (" << default_value << "))";

        return fun.str();
    }

    std::string _lean_expr() const override {
        std::ostringstream expr;
        expr << "({toFun := " << _fun_expr();
        for (int i = 0; i < _dims; i++) {
            expr << ", dom" << i << " := " << std::make_shared<MzIntSetRange>(std::make_shared<MzIntLit>(_ranges[i].first), std::make_shared<MzIntLit>(_ranges[i].second))->lean_expr();
        }
        expr << "} : " << mz_type().lean_name() << ")";
        return expr.str();
    }

    std::string safe_expr() const override {
        std::string expr = "";
        for (const auto& element : _elements) {
            expr = prop_and_default_true(expr, element->safe_expr());
        }
        return expr;
    }

    std::string array_range_expr_at(int dimension) const {
        return std::make_shared<MzIntSetRange>(std::make_shared<MzIntLit>(_ranges[dimension].first), std::make_shared<MzIntLit>(_ranges[dimension].second))->lean_expr();
    }
};


class MzArrayView : public MzTerm {
private:
    std::shared_ptr<MzTerm> _array;
    std::vector<std::shared_ptr<MzTerm>> _indices;
public:
    MzArrayView(std::shared_ptr<MzTerm> array, std::vector<std::shared_ptr<MzTerm>> indices)
        : MzTerm(MzType::array(array->mz_type().inner_type(), indices.size()), false), _array(array), _indices(indices) {
        if (!array->mz_type().is_array()) {
            die("MzArrayView: array must be an array");
        }
        if (array->mz_type().array_dims() != 1) {
            die("MzArrayView: base array must have dimension 1");
        }
        for (const auto& index : _indices) {
            if (index->mz_type() != MzType::set(MzType::int_type())) {
                die("MzArrayView: all index sets must be int sets");
            }
        }
    }

    std::string _lean_expr() const override {
        std::ostringstream expr;
        std::string arr_name = make_unique_varname();
        expr << "let " << arr_name << " := " << _array->lean_expr() << "; ";
        expr << "({toFun := ";
        {
            expr << "fun ";
            std::vector<std::string> var_names;
            for (const auto& index : _indices) {
                var_names.push_back(make_unique_varname());
                expr << var_names.back() << " ";
            }
            expr << "=> ";

            auto domMin = [&](int d) {
                return _indices[d]->min_expr();
            };
            auto domMax = [&](int d) {
                return _indices[d]->max_expr();
            };
            auto len = [&](int d) {
                return "(" + domMax(d) + " - " + domMin(d) + " + 1)";
            };

            std::string lin = "(" + var_names[0] + " - " + domMin(0) + ")";
            for (int d = 1; d < static_cast<int>(_indices.size()); ++d) {
                lin = "(" + lin + " * " + len(d) + " + (" + var_names[d] + " - " + domMin(d) + "))";
            }

            expr << arr_name << ".toFun (" << lin << " + ";
            expr << arr_name << ".dom0.min." + LEAN_UNTOP_D + " 0";
            expr << ")";
        }
        for (size_t i = 0; i < _indices.size(); i++) {
            expr << ", dom" << i << " := " << _indices[i]->lean_expr();
        }
        expr << "} : " << mz_type().lean_name() << ")";
        return expr.str();
    }

    std::string safe_expr() const override {
        std::string expr = _array->safe_expr();
        for (const auto& index : _indices) {
            expr = prop_and_default_true(expr, index->safe_expr());
        }

        std::vector<std::string> vars(_indices.size());
        for (size_t i = 0; i < _indices.size(); ++i) {
            vars[i] = make_unique_varname();
        }

        auto dom_min = [&](size_t d) {
            return _indices[d]->min_expr();
        };
        auto dom_max = [&](size_t d) {
            return _indices[d]->max_expr();
        };
        auto len = [&](size_t d) {
            return "(" + dom_max(d) + " - " + dom_min(d) + " + 1)";
        };

        std::string arr_dom0 = _array->array_range_expr_at(0);
        expr = prop_and_default_true(expr, "mzIsContiguousIntSet (" + arr_dom0 + ")");
        for (const auto& index : _indices) {
            expr = prop_and_default_true(expr, "mzIsContiguousIntSet (" + index->lean_expr() + ")");
        }

        if (!_indices.empty()) {
            std::string lin = "(" + vars[0] + " - " + dom_min(0) + ")";
            for (size_t d = 1; d < _indices.size(); ++d) {
                lin = "(" + lin + " * " + len(d) + " + (" + vars[d] + " - " + dom_min(d) + "))";
            }

            std::string arr_min = "(" + arr_dom0 + ").min." + LEAN_UNTOP_D + " 0";
            std::string idx_expr = "(" + lin + " + " + arr_min + ")";
            std::string access = idx_expr + " \u2208 (" + arr_dom0 + ")";

            std::string quantified = access;
            for (int i = static_cast<int>(_indices.size()) - 1; i >= 0; --i) {
                quantified = "\u2200 " + vars[i] + " \u2208 " + _indices[i]->lean_expr() + ", " + quantified;
            }
            expr = prop_and_default_true(expr, quantified);
        }

        return expr;
    }
};
