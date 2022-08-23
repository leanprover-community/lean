/* Copyright 2019 E.W.Ayers
Authors: E.W.Ayers, R.Y.Lewis */
#define _USE_MATH_DEFINES
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_int.h"
#include <cmath>
#include <limits>

namespace lean{
// [TODO] make a typedef or template for `float` so can generalise to other IEEE-754 impls.
struct vm_float : public vm_external {
    float m_val;
    vm_float(float v) : m_val(v) {}
    virtual ~vm_float() {}
    virtual void dealloc() override {
        this->~vm_float();
        get_vm_allocator().deallocate(sizeof(vm_float), this);
    }
    virtual vm_external * ts_clone(vm_clone_fn const &) override {return new vm_float(m_val);}
    virtual vm_external * clone(vm_clone_fn const &) override {
        return new (get_vm_allocator().allocate(sizeof(vm_float))) vm_float(m_val);
    }
    virtual unsigned int hash() override { return std::hash<float>{}(m_val); }
};

static vm_obj mk_vm_float(float d) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_float))) vm_float(d));
}

vm_obj to_obj(float d) {
    return mk_vm_float(d);
}

float to_float(vm_obj const & o) {
    auto ext_vm_float = dynamic_cast<vm_float*>(to_external(o));
    lean_vm_check(ext_vm_float);
    return ext_vm_float->m_val;
}

vm_obj float_of_nat(vm_obj const & a) {
    return is_simple(a) ? mk_vm_float(cidx(a)) : mk_vm_float(to_mpz(a).get_double());
}
vm_obj float_of_int(vm_obj const & i) {
    return is_simple(i) ? mk_vm_float(to_int(i)) : mk_vm_float(to_mpz(i).get_double());
}

vm_obj float_repr(vm_obj const & a) {
    std::ostringstream out;
    float f = to_float(a);
    out << f;
    return to_obj(out.str());
}

vm_obj float_of_string(vm_obj const & s) {
    try {
        return mk_vm_some(mk_vm_float(std::stof(to_string(s))));
    } catch (std::invalid_argument const & e) {
        return mk_vm_none();
    }
}

void initialize_vm_float() {
    DECLARE_VM_BUILTIN(name({"native", "float", "specification", "radix"}),     []() { return mk_vm_nat(std::numeric_limits<float>::radix); });
    DECLARE_VM_BUILTIN(name({"native", "float", "specification", "precision"}), []() { return mk_vm_nat(std::numeric_limits<float>::digits);});
    DECLARE_VM_BUILTIN(name({"native", "float", "specification", "emax"}),      []() { return mk_vm_nat(std::numeric_limits<float>::max_exponent);});
    DECLARE_VM_BUILTIN(name({"native", "float", "specification", "emin"}),      []() { return mk_vm_int(std::numeric_limits<float>::min_exponent);});
    DECLARE_VM_BUILTIN(name({"native", "float", "epsilon"}),     []() {return mk_vm_float(std::numeric_limits<float>::epsilon()); });
    DECLARE_VM_BUILTIN(name({"native", "float", "round_error"}), []() {return mk_vm_float(std::numeric_limits<float>::round_error());});
    DECLARE_VM_BUILTIN(name({"native", "float", "infinity"}),    []() {return mk_vm_float(std::numeric_limits<float>::infinity()); });
    DECLARE_VM_BUILTIN(name({"native", "float", "qNaN"}),        []() {return mk_vm_float(std::numeric_limits<float>::quiet_NaN()); });
    DECLARE_VM_BUILTIN(name({"native", "float", "sNaN"}),        []() {return mk_vm_float(std::numeric_limits<float>::signaling_NaN()); });

    DECLARE_VM_BUILTIN(name({"native", "float", "is_infinite"}), [](vm_obj const & f) {return mk_vm_bool(std::isinf(to_float(f))); });
    DECLARE_VM_BUILTIN(name({"native", "float", "is_finite"}),   [](vm_obj const & f) {return mk_vm_bool(std::isfinite(to_float(f))); });
    DECLARE_VM_BUILTIN(name({"native", "float", "is_nan"}),      [](vm_obj const & f) {return mk_vm_bool(std::isnan(to_float(f))); });
    DECLARE_VM_BUILTIN(name({"native", "float", "is_normal"}),   [](vm_obj const & f) {return mk_vm_bool(std::isnormal(to_float(f))); });
    DECLARE_VM_BUILTIN(name({"native", "float", "sign"}),        [](vm_obj const & f) {return mk_vm_bool(std::signbit(to_float(f))); });

    DECLARE_VM_BUILTIN(name({"native", "float", "exponent"}), [](vm_obj const & a) {
        float f = to_float(a);
        return std::isfinite(f) ? mk_vm_some(mk_vm_int(std::ilogb(f))) : mk_vm_none();
    });
    DECLARE_VM_BUILTIN(name({"native", "float", "frexp"}), [](vm_obj const & f) {
        int i;
        float m = std::frexp(to_float(f), &i);
        return mk_vm_pair(mk_vm_float(m), mk_vm_int(i));
    });
    DECLARE_VM_BUILTIN(name({"native", "float", "modf"}), [](vm_obj const & f) {
        float i;
        float m = std::modf(to_float(f), &i);
        return mk_vm_pair(mk_vm_float(i), mk_vm_float(m));
    });

    DECLARE_VM_BUILTIN(name({"native", "float", "add"}),   [](vm_obj const & a1, vm_obj const & a2) {return mk_vm_float(to_float(a1) + to_float(a2));});
    DECLARE_VM_BUILTIN(name({"native", "float", "sub"}),   [](vm_obj const & a1, vm_obj const & a2) {return mk_vm_float(to_float(a1) - to_float(a2));});
    DECLARE_VM_BUILTIN(name({"native", "float", "mul"}),   [](vm_obj const & a1, vm_obj const & a2) {return mk_vm_float(to_float(a1) * to_float(a2));});
    DECLARE_VM_BUILTIN(name({"native", "float", "div"}),   [](vm_obj const & a1, vm_obj const & a2) {return mk_vm_float(to_float(a1) / to_float(a2));});
    DECLARE_VM_BUILTIN(name({"native", "float", "pow"}),   [](vm_obj const & a1, vm_obj const & a2) {return mk_vm_float(std::pow(to_float(a1), to_float(a2)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "atan2"}), [](vm_obj const & a1, vm_obj const & a2) {return mk_vm_float(std::atan2(to_float(a1), to_float(a2)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "fmod"}),  [](vm_obj const & a1, vm_obj const & a2) {return mk_vm_float(std::fmod(to_float(a1), to_float(a2)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "remainder"}), [](vm_obj const & a1, vm_obj const & a2) {return mk_vm_float(std::remainder(to_float(a1), to_float(a2)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "max"}),   [](vm_obj const & a1, vm_obj const & a2) {return mk_vm_float(std::fmax(to_float(a1), to_float(a2)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "min"}),   [](vm_obj const & a1, vm_obj const & a2) {return mk_vm_float(std::fmin(to_float(a1), to_float(a2)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "hypot"}), [](vm_obj const & a1, vm_obj const & a2) {return mk_vm_float(std::hypot(to_float(a1), to_float(a2)));});

    DECLARE_VM_BUILTIN(name({"native", "float", "neg"}),   [](vm_obj const & a) {return mk_vm_float(-(to_float(a)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "sqrt"}),  [](vm_obj const & a) {return mk_vm_float(std::sqrt(to_float(a)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "cbrt"}),  [](vm_obj const & a) {return mk_vm_float(std::cbrt(to_float(a)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "abs"}),   [](vm_obj const & a) {return mk_vm_float(std::abs(to_float(a)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "ceil"}),  [](vm_obj const & a) {return mk_vm_int(std::ceil(to_float(a)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "floor"}), [](vm_obj const & a) {return mk_vm_int(std::floor(to_float(a)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "trunc"}), [](vm_obj const & a) {return mk_vm_int(std::trunc(to_float(a)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "round"}), [](vm_obj const & a) {return mk_vm_int(std::round(to_float(a)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "exp"}),   [](vm_obj const & a) {return mk_vm_float(std::exp(to_float(a)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "exp2"}),  [](vm_obj const & a) {return mk_vm_float(std::exp2(to_float(a)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "log"}),   [](vm_obj const & a) {return mk_vm_float(std::log(to_float(a)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "log2"}),  [](vm_obj const & a) {return mk_vm_float(std::log2(to_float(a)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "log10"}), [](vm_obj const & a) {return mk_vm_float(std::log10(to_float(a)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "sin"}),   [](vm_obj const & a) {return mk_vm_float(std::sin(to_float(a)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "cos"}),   [](vm_obj const & a) {return mk_vm_float(std::cos(to_float(a)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "tan"}),   [](vm_obj const & a) {return mk_vm_float(std::tan(to_float(a)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "asin"}),  [](vm_obj const & a) {return mk_vm_float(std::asin(to_float(a)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "acos"}),  [](vm_obj const & a) {return mk_vm_float(std::acos(to_float(a)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "atan"}),  [](vm_obj const & a) {return mk_vm_float(std::atan(to_float(a)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "sinh"}),  [](vm_obj const & a) {return mk_vm_float(std::sinh(to_float(a)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "cosh"}),  [](vm_obj const & a) {return mk_vm_float(std::cosh(to_float(a)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "tanh"}),  [](vm_obj const & a) {return mk_vm_float(std::tanh(to_float(a)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "asinh"}), [](vm_obj const & a) {return mk_vm_float(std::asinh(to_float(a)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "acosh"}), [](vm_obj const & a) {return mk_vm_float(std::acosh(to_float(a)));});
    DECLARE_VM_BUILTIN(name({"native", "float", "atanh"}), [](vm_obj const & a) {return mk_vm_float(std::atanh(to_float(a)));});

    DECLARE_VM_BUILTIN(name({"native", "float", "pi"}),    [](){return mk_vm_float(M_PI);});

    DECLARE_VM_BUILTIN(name({"native", "float", "lt"}),      [](vm_obj const & a1, vm_obj const & a2) {return mk_vm_bool(to_float(a1) < to_float(a2));});
    DECLARE_VM_BUILTIN(name({"native", "float", "le"}),      [](vm_obj const & a1, vm_obj const & a2) {return mk_vm_bool(to_float(a1) <= to_float(a2));});
    DECLARE_VM_BUILTIN(name({"native", "float", "dec_eq"}),  [](vm_obj const & a1, vm_obj const & a2) {return mk_vm_bool(to_float(a1) == to_float(a2));});
    DECLARE_VM_BUILTIN(name({"native", "float", "of_nat"}),  float_of_nat);
    DECLARE_VM_BUILTIN(name({"native", "float", "of_int"}),  float_of_int);
    DECLARE_VM_BUILTIN(name({"native", "float", "to_repr"}), float_repr);
    DECLARE_VM_BUILTIN(name({"native", "float", "of_string"}), float_of_string);
}
void finalize_vm_float() {
}
}
