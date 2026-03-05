#pragma once

#include "config.hpp"
#include "mz_type.hpp"
#include "mz_term_fwd.hpp"

#include <memory>
#include <string>
#include <vector>
#include <sstream>
#include <typeinfo>


class MzTerm {
protected:
    virtual std::string _lean_expr() const {
        die("not implemented");
    };
    const MzType _mzType;
    const bool _single_token;
public:
    virtual ~MzTerm() = default;
    MzTerm(MzType mzType, bool single_token = false) : _mzType(mzType), _single_token(single_token) {
    }

    virtual std::string lean_expr() const {
        return _single_token ? _lean_expr() : "(" + _lean_expr() + ")";
    }

    MzType mz_type() const {
        return _mzType;
    }

    virtual std::string safe_expr() const {
        die("not implemented");
    }

    virtual std::string min_expr() {
        return "(" + lean_expr() + ".min." + LEAN_UNTOP_D + " 0" + ")";
    }

    virtual std::string max_expr() {
        return "(" + lean_expr() + ".max." + LEAN_UNBOT_D + " 0" + ")";
    }

    int array_dims() const {
        if (!mz_type().is_array()) {
            die("MzArrayLike: type must be an array type");
        }
        return mz_type().array_dims();
    }

    /**
     * Returns the Lean expression for the range at the given dimension.
     * NOTE: It is the CALLER's responsibility to call safe_expr() on the this object in its own safe_expr() if it uses array_range_expr_at().
     */
    virtual std::string array_range_expr_at(int dimension) const {
        if (!mz_type().is_array()) {
            die("MzArrayLike: type must be an array type");
        }
        return this->lean_expr() + ".dom" + std::to_string(dimension);
    }

    /**
     * Returns the Lean expression for the element at the given indices.
     * NOTE: It is the CALLER's responsibility to call safe_expr() on the indices in its own safe_expr(), if the indices could contain partiality violations.
     */
    virtual std::string array_element_at(const std::vector<std::shared_ptr<MzTerm>>& indices) const {
        if (!mz_type().is_array()) {
            die("MzArrayLike: type must be an array type");
        }
        std::string out = "(" + this->lean_expr() + ".toFun ";

        for (size_t i = 0; i < indices.size(); i++) {
            out += "(" + indices[i]->lean_expr() + ") ";
        }
        out += ")";

        return out;
    }

    virtual bool is_nonempty_set() const {
        return false;
    }

    virtual std::string array_element_at(const std::vector<std::string>& indices) const {
        if (!mz_type().is_array()) {
            die("MzArrayLike: type must be an array type");
        }
        std::string out = "(" + this->lean_expr() + ".toFun ";
    
        for (size_t i = 0; i < indices.size(); i++) {
            out += "(" + indices[i] + ") ";
        }
        out += ")";
    
        return out;
    }

};
