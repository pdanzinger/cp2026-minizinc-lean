#pragma once

#include "mz_terms_all.hpp"
#include "compiler_state.hpp"
#include "library_functions.hpp"
#include "utils.hpp"

#include <minizinc/ast.hh>

#include <memory>
#include <string>
#include <tuple>
#include <vector>

using namespace MiniZinc;


class MzExpressionParser {
protected:
    std::shared_ptr<MzTerm> parseIntLit(CompilerState& cs, IntLit* il) {
        enforce_non_opt(il);
        return std::make_shared<MzIntLit>(IntLit::v(il).toInt());
    }

    std::shared_ptr<MzTerm> parseFloatLit(CompilerState& cs, FloatLit* fl) {
        die("Float lits not supported");
    }

    std::shared_ptr<MzTerm> parseSetLit(CompilerState& cs, SetLit* sl) {
        enforce_non_opt(sl);
        if (sl->fsv() != nullptr) {
            die("Float set lits not supported");
        }
        if (sl->isv() != nullptr) {
            auto lb = std::make_shared<MzIntLit>(sl->isv()->min().toInt());
            auto ub = std::make_shared<MzIntLit>(sl->isv()->max().toInt());
            return std::make_shared<MzIntSetRange>(lb, ub);
        }

        std::vector<std::shared_ptr<MzTerm>> vals;
        MzType base_type = mz_type_from_type(Expression::type(sl)).base_type();
        if (base_type != MzType::int_type() && base_type != MzType::bool_type()) {
            die("Unsupported Set literal content.");
        }
        for (auto* expr : sl->v()) {
            auto parsed = parseExpression(cs, expr);
            if (parsed->mz_type() != base_type) {
                die("Unsupported Set literal content.");
            }
            vals.push_back(parsed);
        }
        return std::make_shared<MzSetLit>(vals, base_type);
    }

    std::shared_ptr<MzTerm> parseBoolLit(CompilerState& cs, BoolLit* bl) {
        enforce_non_opt(bl);
        return std::make_shared<MzBoolLit>(bl->v());
    }

    std::shared_ptr<MzTerm> parseStringLit(CompilerState& cs, StringLit* sl) {
        enforce_non_opt(sl);
        die("String lits not supported");
    }

    std::shared_ptr<MzTerm> parseId(CompilerState& cs, Id* id) {
        enforce_non_opt(id);
        if (!id->hasStr()) {
            die("Unsupported, id without str");
        }

        cs.ensure_id_present(id);
        std::string name(id->v().c_str());
        Identifier identifier(cs, name);


        auto var_decl = std::dynamic_pointer_cast<MzVarDecl>(parseExpression(cs, id->decl()));
        if (var_decl == nullptr) {
            die("Could not parse var decl");
        }

        return std::make_shared<MzId>(identifier, var_decl);
    }

    std::shared_ptr<MzTerm> parseAnonVar(CompilerState& cs, AnonVar* av) {
        die("Unsupported Expression: parseAnonVar");
    }

    std::shared_ptr<MzTerm> parseArrayLit(CompilerState& cs, ArrayLit* al) {
        if (al->isTuple()) {
            die("Unsupported Expression: parseArrayLit tuple");
        }
        int dims = al->dims();
        std::vector<std::pair<int, int>> ranges;
        for (int d = 0; d < dims; d++) {
            ranges.push_back(std::make_pair(al->min(d), al->max(d)));
        }
        std::vector<std::shared_ptr<MzTerm>> elements;
        for (int i = 0; i < al->length(); i++) {
            elements.push_back(parseExpression(cs, (*al)[i]));
        }
        const MzType t = mz_type_from_type(Expression::type(al));
        if (!t.is_array()) {
            die("parseArrayLit: expected array type");
        }
        if (t.array_dims() != dims) {
            die("parseArrayLit: internal error, dimension mismatch");
        }
        return std::make_shared<MzArrayLit>(dims, ranges, elements, t.inner_type());
    }

    std::shared_ptr<MzTerm> parseArrayAccess(CompilerState& cs, ArrayAccess* aa) {
        /*
        if (Expression::eid(aa->v()) != Expression::E_ID) {
            die("not implemented. shouldn't happen?");
        }
        auto id = Expression::cast<Id>(aa->v());
        std::string name(id->v().c_str());
        Identifier identifier(cs, name);
        std::shared_ptr<MzTerm> id_term = parseExpression(cs, id);
        */
        std::shared_ptr<MzTerm> inner_term = parseExpression(cs, aa->v());

        std::vector<std::shared_ptr<MzTerm>> indices;
        for (const auto& idx : aa->idx()) {
            indices.push_back(parseExpression(cs, idx));
        }

        return std::make_shared<MzArrayAccess>(inner_term, indices);
    }

    std::shared_ptr<MzTerm> parseFieldAccess(CompilerState& cs, FieldAccess* fa) {
        die("Unsupported Expression: parseFieldAccess");
    }

    std::tuple<std::vector<std::shared_ptr<MzTerm>>, std::vector<Identifier>, std::shared_ptr<MzTerm>, std::shared_ptr<MzTerm>> _preParseComprehension(CompilerState& cs, Comprehension* comp) {
        bool where_used = false;
        std::shared_ptr<MzTerm> where_expr = std::make_shared<MzBoolLit>(true);

        std::vector<std::string> local_var_names;
        std::vector<Identifier> vars;          // list of identifiers for bound variables
        std::vector<std::shared_ptr<MzTerm>> domains;     // list of set terms for generators, same length as local_var_names

        for (int gen_id = 0; gen_id < comp->numberOfGenerators(); gen_id++) {
            auto set_term = parseExpression(cs, comp->in(gen_id));

            for (int decl_id = 0; decl_id < comp->numberOfDecls(gen_id); decl_id++) {
                auto vd = comp->decl(gen_id, decl_id);
                std::string var_name(vd->id()->v().c_str());
                if (std::find(local_var_names.begin(), local_var_names.end(), var_name) != local_var_names.end()) {
                    // Supporting this would mean we can't just collect the where clauses into a single expression.
                    // E.g. recursion needed instead, but currently this would mean a lot of "boxing/unboxing" of lambdas in the resulting lean code.
                    die("Unsupported -- duplicate variable name inside comprehension");
                }
                cs.add_local_var_name(var_name);
                local_var_names.push_back(var_name);
                vars.push_back(Identifier(cs, var_name));
                domains.push_back(set_term);
            }

            if (comp->where(gen_id) != nullptr) {
                auto where = parseExpression(cs, comp->where(gen_id));
                where_expr = where_used ? std::make_shared<MzBinOpBool>(where_expr, where, BOT_AND) : where;
                where_used = true;
            }
        }
        auto body = parseExpression(cs, comp->e());

        for (const std::string& var_name : local_var_names) {
            cs.remove_last_local_var_name();
        }

        if (!where_used) {
            where_expr = nullptr;
        }

        return std::make_tuple(domains, vars, body, where_expr);
    }

    /*
    collapse_dims: if true, then the dimensions of the comprehension are collapsed into a single dimension. (default for minizinc array literals)
    */
    std::shared_ptr<MzTerm> parseComprehension(CompilerState& cs, Comprehension* comp, bool collapse_dims = true) {
        auto [domains, vars, body, where_expr] = _preParseComprehension(cs, comp);


        if (comp->set()) {
            if (comp->numberOfGenerators() == 1 && comp->numberOfDecls(0) == 1) {
                return std::make_shared<MzSetComprehension>(domains[0], vars[0], body, where_expr);
            }
            die("parseComprehension: unsupported: set literal with multiple generators or declarations");
        }


        if (where_expr != nullptr) {
            die("parseComprehension: where_expr in array comprehension not supported");
        }


        std::shared_ptr<MzArrayComprehension> array_comprehension = std::make_shared<MzArrayComprehension>(domains, vars, body, collapse_dims);
        return array_comprehension;
    }

    std::shared_ptr<MzTerm> parseITE(CompilerState& cs, ITE* ite) {
        std::vector<std::shared_ptr<MzTerm>> conditions;
        std::vector<std::shared_ptr<MzTerm>> then_exprs;
        for (int i = 0; i < ite->size(); i++) {
            conditions.push_back(parseExpression(cs, ite->ifExpr(i)));
            then_exprs.push_back(parseExpression(cs, ite->thenExpr(i)));
        }
        auto else_expr = parseExpression(cs, ite->elseExpr());
        return std::make_shared<MzITE>(conditions, then_exprs, else_expr);
    }

    std::shared_ptr<MzTerm> parseBinOp(CompilerState& cs, BinOp* bo) {
        auto lhs = parseExpression(cs, bo->lhs());
        auto rhs = parseExpression(cs, bo->rhs());

        if (bo->op() == BinOpType::BOT_DOTDOT) {
            // special case
            return std::make_shared<MzIntSetRange>(lhs, rhs);
        }

        if (MzBinOpCmp::binOpToLeanSymbol.count(bo->op()) > 0) {
            return std::make_shared<MzBinOpCmp>(lhs, rhs, bo->op());
        }
        if (MzBinOpArith::binOpToLeanSymbolAscii.count(bo->op()) > 0) {
            return std::make_shared<MzBinOpArith>(lhs, rhs, bo->op());
        }
        if (MzBinOpBool::binOpToLeanSymbolAscii.count(bo->op()) > 0) {
            return std::make_shared<MzBinOpBool>(lhs, rhs, bo->op());
        }
        if (bo->op() == BinOpType::BOT_IN) {
            return std::make_shared<MzSetMembership>(lhs, rhs);
        }
        if (bo->op() == BOT_UNION || bo->op() == BOT_DIFF || bo->op() == BOT_INTERSECT) {
            return std::make_shared<MzBinOpSet>(lhs, rhs, bo->op());
        }
        if (bo->op() == BOT_PLUSPLUS) {
            die("Unsupported Operation '++': arrays concatenation not supported");
            return nullptr;
        }
        die("Unsupported Operation: " + std::to_string(bo->op()));
        return nullptr;
    }

    std::shared_ptr<MzTerm> parseUnOp(CompilerState& cs, UnOp* uo) {
        auto term = parseExpression(cs, uo->e());
        auto op = uo->op();
        switch (op) {
            case UOT_NOT:
                return std::make_shared<MzUnOpBool>(term, op);
            case UOT_PLUS:
            case UOT_MINUS:
                return std::make_shared<MzUnOpInt>(term, op);
            default:
                die("Unsupported unary operation: " + std::to_string(op));
                return nullptr;
        }
    }

    std::shared_ptr<MzTerm> parseCall(CompilerState& cs, Call* c) {
        std::string raw_call_name(c->id().c_str());
        std::string call_name = normalize_mzn_call_name(raw_call_name);

        std::cerr << "call: call_name=" << call_name << ", ascii ids: ";
        for (int i = 0; i < call_name.size(); i++) {
            std::cerr << " " << ((int)call_name[i]);
        }
        std::cerr << std::endl;

        // parse binary function calls (min, max)
        if (c->argCount() == 2 && (call_name == "min" || call_name == "max")) {
            return std::make_shared<MzBinFunc>(parseExpression(cs, c->arg(0)), parseExpression(cs, c->arg(1)), call_name == "min" ? MzBinFunc::BinFuncType::MIN : MzBinFunc::BinFuncType::MAX);
        }

        // Parse aggregator calls (forall, exists, sum, min, max)
        {
            std::string kw;
            if (call_name == "forall") kw = call_name;
            if (call_name == "exists") kw = call_name;
            if (call_name == "sum") kw = call_name;
            if (call_name == "min") kw = call_name;
            if (call_name == "max") kw = call_name;
            if (kw.size() > 0) {
                if (c->argCount() != 1) {
                    die("Unsupported -- malformed " + kw + "?");
                }

                auto type = Expression::type(c->arg(0));
                MzAggregator::AggregatorType aggregator_type;
                // min/max for bools get parsed as forall/exists
                if (kw == "forall" || (kw == "min" && type.bt() == Type::BT_BOOL)) {
                    aggregator_type = MzAggregator::AggregatorType::FORALL;
                } else if (kw == "exists" || (kw == "max" && type.bt() == Type::BT_BOOL)) {
                    aggregator_type = MzAggregator::AggregatorType::EXISTS;
                } else if (kw == "sum") {
                    aggregator_type = MzAggregator::AggregatorType::SUM;
                } else if (kw == "min" && (type.bt() == Type::BT_INT || type.bt() == Type::BT_FLOAT)) {
                    aggregator_type = MzAggregator::AggregatorType::MIN;
                } else if (kw == "max" && (type.bt() == Type::BT_INT || type.bt() == Type::BT_FLOAT)) {
                    aggregator_type = MzAggregator::AggregatorType::MAX;
                } else {
                    die("parseCall: internal error, unexpected kw and/or types: " + kw + " with types " + type.simpleToString());
                }


                if (Expression::eid(c->arg(0)) == Expression::E_COMP) {
                    auto comp = Expression::cast<Comprehension>(c->arg(0));

                    // final format example:   forall (i : ...) (j : ...) (b : ...), (i < j) -> b -> <body>
                    //                                <         out_decls         >  <      out_body      >
                    //              constraint forall (i, j in ... where i < j, b in ... where b) (<body>);

                    auto [domains, vars, body, where_expr] = _preParseComprehension(cs, comp);

                    return std::make_shared<MzComprehensionAggregator>(aggregator_type, domains, vars, body, where_expr);
                } else {
                    std::shared_ptr<MzTerm> inner_expr = parseExpression(cs, c->arg(0));
                    return std::make_shared<MzAggregator>(inner_expr, aggregator_type);
                }


            }
        }

        {
            // try to match "array<n>d"
            for (int n = 1; n <= 8; n++) {
                if (call_name.find("array" + std::to_string(n) + "d") != std::string::npos) {
                    if (c->argCount() != n+1) {
                        break; // some edge cases break this rule, dealt with elsewhere
                    }
                    std::vector<std::shared_ptr<MzTerm>> indices;
                    for (int i = 0; i < n; i++) {
                        indices.push_back(parseExpression(cs, c->arg(i)));
                    }

                    std::shared_ptr<MzTerm> array = parseExpression(cs, c->arg(n));
                    return std::make_shared<MzArrayView>(array, indices);
                }
            }
        }

        // Parse all Arguments
        std::vector<std::shared_ptr<MzTerm>> args;
        for (int i = 0; i < c->argCount(); i++) {
            args.push_back(parseExpression(cs, c->arg(i)));
        }

        // Scalar coercions that are easier to model as dedicated IR nodes.
        if (call_name == "bool2int" && args.size() == 1 && args[0]->mz_type() == MzType::bool_type()) {
            return std::make_shared<MzUnFunc>(args[0], MzUnFunc::UnFuncType::BOOL2INT);
        }

        // Implementations
        if (call_name == "cumulative") {
            if (cs.in_target_constraint()) {
                die("cumulative is not allowed inside redundant target constraints");
            }
            if (args.size() != 4) {
                die("MzCumulative: expected 4 arguments");
            }
            return std::make_shared<MzCumulative>(args[0], args[1], args[2], args[3]);
        }
        if (call_name == "all_different" ||
            call_name == "alldifferent") {
            if (args.size() != 1) {
                die("MzAllDifferent: expected 1 argument");
            }
            return std::make_shared<MzAllDifferent>(args[0]);
        }
        if (call_name == "circuit") {
            if (args.size() != 1) {
                die("MzCircuit: expected 1 argument");
            }
            return std::make_shared<MzCircuit>(args[0]);
        }

        {
            auto& gens = get_mzn_library_generators();
            for (const auto& gen : gens) {
                if (gen.applies(call_name, args)) {
                    return gen.generate(args);
                }
            }
        }

        if (c->decl() != nullptr) {
            die("parseCall: function declarations not supported");
        }

        die("parseCall: call not implemented and not declared: " + call_name + "(" + raw_call_name + ")");
    }

    std::shared_ptr<MzVarDecl> parseVarDecl(CompilerState& cs, VarDecl* vd) {
        enforce_non_opt(vd);
        if (!vd->id()->hasStr()) {
            die("Error. Should not happen? Id should have name");
        }
        if (vd->ti()->isEnum()) {
            die("Enums not supported");
        }
        std::string name(vd->id()->v().c_str());
        Identifier identifier(cs, name);

        bool is_set = vd->ti()->type().st() == MiniZinc::Type::ST_SET;
        bool is_array = vd->ti()->isarray();

        MzType mzType = MzType::int_type();
        switch (Expression::type(vd).bt()) {
            case Type::BaseType::BT_INT:
                mzType = MzType::int_type();
                break;
            case Type::BaseType::BT_FLOAT:
                die("MzVarDecl: Unsupported Base Type: FLOAT");
                mzType = MzType::float_type();
                break;
            case Type::BaseType::BT_BOOL:
                mzType = MzType::bool_type();
                break;
            case Type::BaseType::BT_STRING:
                die("MzVarDecl: Unsupported Base Type: STRING");
            default:
                die("MzVarDecl: Unsupported Base Type: " + std::to_string(Expression::type(vd).bt()));
        }
        if (is_set) {
            mzType = MzType::set(mzType);
        }
        if (is_array) {
            mzType = MzType::array(mzType, vd->ti()->ranges().size());
        }


        std::shared_ptr<MzTerm> domain = nullptr;
        if (vd->ti()->domain() != nullptr) {
            domain = parseExpression(cs, vd->ti()->domain());
        }


        std::shared_ptr<MzTerm> definition = nullptr;
        if (vd->e() != nullptr) {
            definition = parseExpression(cs, vd->e());
        }

        std::vector<std::shared_ptr<MzTerm>> ranges;
        if (is_array) {
            for (auto* range : vd->ti()->ranges()) {
                if (range->domain() == nullptr) {
                    ranges.push_back(nullptr);

                    // old, now handled inside MzVarDecl
                    /*
                    // create and register a var decl with a new variable name for a set of int (stand in for int in mzn)
                    std::string new_var_name = make_unique_varname();
                    Identifier new_identifier(cs, new_var_name);
                    std::vector<std::shared_ptr<MzTerm>> new_ranges;
                    auto new_var_decl = std::make_shared<MzVarDecl>(new_identifier, MzType::set(MzType::int_type()), nullptr, nullptr, new_ranges);
                    cs.add_global_var_decl(new_var_decl);
                    ranges.push_back(std::make_shared<MzId>(new_identifier, new_var_decl));
                    */
                } else {
                    ranges.push_back(parseExpression(cs, range->domain()));
                }
            }
        }

        return std::make_shared<MzVarDecl>(identifier, mzType, domain, definition, ranges);
    }

    std::shared_ptr<MzTerm> parseLet(CompilerState& cs, Let* l) {
        // letOrig?
        std::vector<std::shared_ptr<MzVarDecl>> var_decls;
        std::vector<std::shared_ptr<Identifier>> orig_identifiers;
        for (auto* binding : l->let()) {
            if (Expression::eid(binding) != Expression::E_VARDECL) {
                die("Unsupported Expression: parseLet where binding is not a var decl");
            }
            auto vd = Expression::cast<VarDecl>(binding);

            std::string mzn_name(vd->id()->v().c_str());
            std::shared_ptr<Identifier> orig_identifier = nullptr;
            if (cs.has_var_name(mzn_name)) {
                //// Note: this is disallowed, because we need to add the var name to local var names BEFORE parsing the var decl
                //// Otherwise, the var decl would use "model." for the definition, which is wrong in lean "let in"
                //// But in minizinc, the "let in" may shadow an outer variable. If that happens, the reference would be wrong here, so we just disallow it.
                if (cs.has_global_var_name(mzn_name) && !cs.has_local_var_name(mzn_name)) {
                    //die()
                    // note: this case is also okay with backup_global_name
                    orig_identifier = std::make_shared<Identifier>(cs, mzn_name);
                }
                //die("Unsupported Expression: parseLet, var decl has duplicate name");
            }
            cs.add_local_var_name(mzn_name);
            Identifier identifier(cs, mzn_name);

            std::shared_ptr<MzVarDecl> var_decl = std::dynamic_pointer_cast<MzVarDecl>(parseExpression(cs, vd));
            var_decls.push_back(var_decl);
            orig_identifiers.push_back(orig_identifier);
        }
        std::shared_ptr<MzTerm> body = parseExpression(cs, l->in());
        for (auto var_name : var_decls) {
            cs.remove_last_local_var_name();
        }
        return std::make_shared<MzLetIn>(var_decls, orig_identifiers, body);
    }

    std::shared_ptr<MzTerm> parseTypeInst(CompilerState& cs, TypeInst* ti) {
        die("Unsupported Expression: parseTypeInst");
    }

    std::shared_ptr<MzTerm> parseTIId(CompilerState& cs, TIId* tiid) {
        die("Unsupported Expression: parseTIId");
    }

public:
    std::shared_ptr<MzTerm> parseExpression(CompilerState& cs, Expression* e) {
        if (cs.has_parsed_expression(e)) {
            return cs.get_parsed_expression(e);
        }
        std::cerr << "--expr at loc " << Expression::loc(e).toString() << std::endl;
        std::shared_ptr<MzTerm> parsed_expression;
        switch (Expression::eid(e)) {
            case Expression::E_INTLIT:
                parsed_expression = parseIntLit(cs, Expression::cast<IntLit>(e));
                break;
            case Expression::E_FLOATLIT:
                parsed_expression = parseFloatLit(cs, Expression::cast<FloatLit>(e));
                break;
            case Expression::E_SETLIT:
                parsed_expression = parseSetLit(cs, Expression::cast<SetLit>(e));
                break;
            case Expression::E_BOOLLIT:
                parsed_expression = parseBoolLit(cs, Expression::cast<BoolLit>(e));
                break;
            case Expression::E_STRINGLIT:
                parsed_expression = parseStringLit(cs, Expression::cast<StringLit>(e));
                break;
            case Expression::E_ID:
                parsed_expression = parseId(cs, Expression::cast<Id>(e));
                break;
            case Expression::E_ANON:
                parsed_expression = parseAnonVar(cs, Expression::cast<AnonVar>(e));
                break;
            case Expression::E_ARRAYLIT:
                parsed_expression = parseArrayLit(cs, Expression::cast<ArrayLit>(e));
                break;
            case Expression::E_ARRAYACCESS:
                parsed_expression = parseArrayAccess(cs, Expression::cast<ArrayAccess>(e));
                break;
            case Expression::E_FIELDACCESS:
                parsed_expression = parseFieldAccess(cs, Expression::cast<FieldAccess>(e));
                break;
            case Expression::E_COMP:
                parsed_expression = parseComprehension(cs, Expression::cast<Comprehension>(e));
                break;
            case Expression::E_ITE:
                parsed_expression = parseITE(cs, Expression::cast<ITE>(e));
                break;
            case Expression::E_BINOP:
                parsed_expression = parseBinOp(cs, Expression::cast<BinOp>(e));
                break;
            case Expression::E_UNOP:
                parsed_expression = parseUnOp(cs, Expression::cast<UnOp>(e));
                break;
            case Expression::E_CALL:
                parsed_expression = parseCall(cs, Expression::cast<Call>(e));
                break;
            case Expression::E_VARDECL:
                parsed_expression = parseVarDecl(cs, Expression::cast<VarDecl>(e));
                break;
            case Expression::E_LET:
                parsed_expression = parseLet(cs, Expression::cast<Let>(e));
                break;
            case Expression::E_TI:
                parsed_expression = parseTypeInst(cs, Expression::cast<TypeInst>(e));
                break;
            case Expression::E_TIID:
                parsed_expression = parseTIId(cs, Expression::cast<TIId>(e));
                break;
            default:
                die("Unsupported Expression: unaccounted case in parseExpression switch");
        }
        cs.add_parsed_expression(e, parsed_expression);
        return parsed_expression;
    }
};
