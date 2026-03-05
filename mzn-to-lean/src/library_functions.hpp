#pragma once

#include "mz_terms_all.hpp"

#include <functional>
#include <memory>
#include <string>
#include <vector>
#include <sstream>



class MzLibraryFunction : public MzTerm {
private:
    std::string _name;
    std::vector<std::shared_ptr<MzTerm>> _args;
    std::function<std::string(const std::vector<std::shared_ptr<MzTerm>>&)> _lean_expr_fn;

public:
    MzLibraryFunction(
        std::string name,
        std::vector<std::shared_ptr<MzTerm>> args,
        MzType return_type,
        std::function<std::string(const std::vector<std::shared_ptr<MzTerm>>&)> lean_expr_fn
    )
    : MzTerm(return_type, false),
        _name(std::move(name)),
        _args(std::move(args)),
        _lean_expr_fn(std::move(lean_expr_fn)) {
        if (!_lean_expr_fn) {
            die("MzLibraryFunction: missing lean expression callback");
        }
    }

    std::string _lean_expr() const override {
        return _lean_expr_fn(_args);
    }

    std::string safe_expr() const override {
        std::string expr = "";
        for (const auto& arg : _args) {
            expr = prop_and_default_true(expr, arg->safe_expr());
        }
        return expr;
    }
};


class MzLibraryFunctionGenerator {
public:
    using LeanExprFn = std::function<std::string(const std::vector<std::shared_ptr<MzTerm>>&)>; // builds Lean expr from args
    using TypeFn     = std::function<MzType(const std::vector<std::shared_ptr<MzTerm>>&)>;       // computes return type from args
    using FilterFn   = std::function<bool(const std::vector<std::shared_ptr<MzTerm>>&)>;         // extra guard

private:
    std::string _name;
    int _arg_count;
    LeanExprFn _lean_expr_fn;
    TypeFn _type_fn;
    FilterFn _filter_fn;

public:
    MzLibraryFunctionGenerator(
        std::string name,
        int arg_count,
        LeanExprFn lean_expr_fn,
        TypeFn type_fn,
        FilterFn filter_fn = nullptr
    )
    : _name(std::move(name)),
        _arg_count(arg_count),
        _lean_expr_fn(std::move(lean_expr_fn)),
        _type_fn(std::move(type_fn)),
        _filter_fn(std::move(filter_fn)) {
        if (!_lean_expr_fn) {
            die("MzLibraryFunctionGenerator: missing lean expr function");
        }
        if (!_type_fn) {
            die("MzLibraryFunctionGenerator: missing type function");
        }
        if (!_filter_fn) {
            // default filter that always applies
            _filter_fn = [](const std::vector<std::shared_ptr<MzTerm>>&) { return true; };
        }
    }

    bool applies(const std::string& name, const std::vector<std::shared_ptr<MzTerm>>& args) const {
        if (name != _name) return false;
        if (static_cast<int>(args.size()) != _arg_count) return false;
        return _filter_fn(args);
    }

    std::shared_ptr<MzLibraryFunction> generate(const std::vector<std::shared_ptr<MzTerm>>& args) const {
        // Compute the return type based on arguments
        MzType ty = _type_fn(args);
        return std::make_shared<MzLibraryFunction>(_name, args, ty, _lean_expr_fn);
    }
};


static std::vector<MzLibraryFunctionGenerator>& get_mzn_library_generators() {
    static std::vector<MzLibraryFunctionGenerator> gens;

    // Initialize once
    if (gens.empty()) {
        // card(S) : Int
        gens.emplace_back(
            "card",
            1,
            [](const std::vector<std::shared_ptr<MzTerm>>& a) -> std::string {
                return "Int.ofNat (" + a[0]->lean_expr() + ".card)";
            },
            [](const std::vector<std::shared_ptr<MzTerm>>& a) -> MzType {
                if (!a[0]->mz_type().is_set()) {
                    die("card: argument must be a set");
                }
                return MzType::int_type();
            }
        );

        // length(A) : Int
        gens.emplace_back(
            "length",
            1,
            [](const std::vector<std::shared_ptr<MzTerm>>& a) -> std::string {
                const MzType& t = a[0]->mz_type();
                if (!t.is_array()) {
                    die("length: argument must be an array");
                }
                int d = t.array_dims();
                return "Int.ofNat (Array" + std::to_string(d) + "d.size " + a[0]->lean_expr() + ")";
            },
            [](const std::vector<std::shared_ptr<MzTerm>>& a) -> MzType {
                if (!a[0]->mz_type().is_array()) {
                    die("length: argument must be an array");
                }
                return MzType::int_type();
            }
        );
        
        gens.emplace_back(
            "mzn_symmetry_breaking_constraint",
            1,
            [](const std::vector<std::shared_ptr<MzTerm>>& a) -> std::string {
                return a[0]->lean_expr();
            },
            [](const std::vector<std::shared_ptr<MzTerm>>& a) -> MzType {
                if (a[0]->mz_type() != MzType::bool_type()) {
                    die("mzn_symmetry_breaking_constraint: expected bool");
                }
                return MzType::bool_type();
            }
        );
        gens.emplace_back(
            "symmetry_breaking_constraint",
            1,
            [](const std::vector<std::shared_ptr<MzTerm>>& a) -> std::string {
                return a[0]->lean_expr();
            },
            [](const std::vector<std::shared_ptr<MzTerm>>& a) -> MzType {
                if (a[0]->mz_type() != MzType::bool_type()) {
                    die("symmetry_breaking_constraint: expected bool");
                }
                return MzType::bool_type();
            }
        );
    }

    return gens;
}
