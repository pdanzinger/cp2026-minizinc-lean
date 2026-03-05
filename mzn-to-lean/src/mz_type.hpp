#pragma once

#include "config.hpp"

#include <string>
#include <memory>

#include <minizinc/ast.hh>

using namespace MiniZinc;

class MzType {
public:
    enum class Kind {
        INT,
        FLOAT,
        BOOL,
        SET,
        ARRAY
    };

private:
    Kind kind_;
    std::shared_ptr<MzType> base_type_; // for SET, OPT_SET, ARRAY
    int dimension_; // for ARRAY only, [1,8]

    // Private constructors
    MzType(Kind k) : kind_(k), base_type_(nullptr), dimension_(0) {}
    MzType(Kind k, const MzType& base) : kind_(k), base_type_(std::make_shared<MzType>(base)), dimension_(0) {}
    MzType(Kind k, const MzType& base, int dim) : kind_(k), base_type_(std::make_shared<MzType>(base)), dimension_(dim) {}

public:
    // Factory methods for scalar types
    static MzType int_type() { return MzType(Kind::INT); }
    static MzType float_type() { return MzType(Kind::FLOAT); }
    static MzType bool_type() { return MzType(Kind::BOOL); }

    // Factory for set - requires non-opt scalar
    static MzType set(const MzType& type) {
        if (!type.is_scalar()) {
            die("set() requires scalar type");
        }
        if (type.is_opt()) {
            die("set() cannot contain opt types");
        }
        return MzType(Kind::SET, type);
    }

    // Factory for array - requires scalar or set, dimension in [1,8]
    static MzType array(const MzType& type, int dimension) {
        if (dimension < 1 || dimension > 8) {
            die("array dimension must be between 1 and 8");
        }
        if (!type.is_scalar() && !type.is_set()) {
            die("array() requires scalar or set type");
        }
        return MzType(Kind::ARRAY, type, dimension);
    }

    // Query methods
    bool is_scalar() const {
        return kind_ == Kind::INT || kind_ == Kind::FLOAT || kind_ == Kind::BOOL;
    }

    bool is_set() const {
        return kind_ == Kind::SET;
    }

    bool is_array() const {
        return kind_ == Kind::ARRAY;
    }

    bool is_int() const {
        return kind_ == Kind::INT;
    }

    bool is_float() const {
        return kind_ == Kind::FLOAT;
    }

    bool is_bool() const {
        return kind_ == Kind::BOOL;
    }

    int array_dims() const {
        if (!is_array()) {
            die("array_dims() called on non-array type");
        }
        return dimension_;
    }

    bool is_opt() const {
        if (is_array()) {
            die("is_opt() called on array type");
        }
        return false;
    }

    MzType inner_type() const {
        if (is_scalar()) {
            die("base_type() called on scalar type");
        }
        if (!base_type_) {
            die("base_type() called but base_type_ is null");
        }
        return *base_type_;
    }

    MzType base_type() const {
        return is_scalar() ? *this : inner_type().base_type();
    }

    // Generate Lean type name
    std::string lean_name() const {
        switch (kind_) {
            case Kind::INT:
                return "Int";
            case Kind::FLOAT:
                return "Float";
            case Kind::BOOL:
                return "Prop";
            case Kind::SET: {
                    return "(Finset " + inner_type().lean_name() + ")";
                }
            case Kind::ARRAY: {
                return "(Array" + std::to_string(dimension_) + "d " + inner_type().lean_name() + ")";
            }
            default:
                die("Unknown type kind");
                return "";
        }
    }

    // Structural equality
    bool operator==(const MzType& other) const {
        if (kind_ != other.kind_) {
            return false;
        }
        if (is_array() && dimension_ != other.dimension_) {
            return false;
        }
        if (base_type_ && other.base_type_) {
            return *base_type_ == *other.base_type_;
        }
        return base_type_ == other.base_type_;
    }

    bool operator!=(const MzType& other) const {
        return !(*this == other);
    }
};

inline MzType mz_type_from_type(const Type& type, TypeInst* ti = nullptr) {
    auto scalar_non_opt = [&]() -> MzType {
        switch (type.bt()) {
            case Type::BT_INT:
                return MzType::int_type();
            case Type::BT_FLOAT:
                return MzType::float_type();
            case Type::BT_BOOL:
                return MzType::bool_type();
            default:
                die("Unsupported Base Type: " + std::to_string(type.bt()));
        }
    };

    auto scalar_opt = [&]() -> MzType {
        switch (type.bt()) {
            case Type::BT_INT:
            default:
                die("Unsupported Optional Base Type: " + std::to_string(type.bt()));
        }
    };

    bool is_set = type.st() == Type::ST_SET;
    bool is_opt = type.ot() == Type::OT_OPTIONAL;

    MzType result = MzType::int_type();
    if (is_set) {
        auto inner = scalar_non_opt();
        if (is_opt) {
            die("Unsupported Optional Base Type: " + std::to_string(type.bt()));
        } else {
            result = MzType::set(inner);
        }
    } else {
        result = is_opt ? scalar_opt() : scalar_non_opt();
    }

    int dims = 0;
    if (ti != nullptr) {
        dims = ti->ranges().size();
    } else {
        dims = type.dim();
    }
    if (dims < 0) {
        dims = 0;
    }
    if (dims > 0) {
        result = MzType::array(result, dims);
    }
    return result;
}
