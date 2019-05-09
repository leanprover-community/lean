/* Authors: E.W.Ayers, R.Y.Lewis */
#include "library/vm/vm.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_int.h"
#include <math.h>

namespace lean{
// [TODO] make a typedef or template for `float` so can generalise to other IEEE-754 impls.
struct vm_float : public vm_external {
    float m_val;
    vm_float(float const & v) : m_val(v) {}
    virtual ~vm_float() {}
    virtual void dealloc() override {
        this->~vm_float();
        get_vm_allocator().deallocate(sizeof(vm_float), this);
    }
    virtual vm_external * ts_clone(vm_clone_fn const &) override {return new vm_float(m_val);}
    virtual vm_external * clone(vm_clone_fn const &) override {
        return new (get_vm_allocator().allocate(sizeof(vm_float))) vm_float(m_val);
    }
};

vm_obj mk_vm_float(float d) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_float))) vm_float(d));
}
optional<float> try_to_float(vm_obj const & o) {
    if (LEAN_LIKELY(is_external(o))) {
        float f = static_cast<vm_float*>(to_external(o))->m_val;
        return optional<float>(f);
    }
    else {
        return optional<float>();
    }
}
float to_float(vm_obj const & o) {
    return try_to_float(o).value();
}

vm_obj spec_radix() { return mk_vm_nat(std::numeric_limits<float>::radix); }
vm_obj spec_precision() {  return mk_vm_nat(std::numeric_limits<float>::digits);}
vm_obj spec_emax() {  return mk_vm_nat(std::numeric_limits<float>::max_exponent);}
vm_obj spec_emin() {  return mk_vm_int(std::numeric_limits<float>::min_exponent);}

vm_obj float_epsilon() {return mk_vm_float(std::numeric_limits<float>::epsilon()); }
vm_obj float_infinity() {return mk_vm_float(std::numeric_limits<float>::infinity()); }
vm_obj float_is_infinite(vm_obj const & f) {return mk_vm_bool(isinf(to_float(f))); }
vm_obj float_is_finite(vm_obj const & f) {return mk_vm_bool(isfinite(to_float(f))); }
vm_obj float_is_nan(vm_obj const & f) {return mk_vm_bool(isnan(to_float(f))); }
vm_obj float_is_normal(vm_obj const & f) {return mk_vm_bool(isnormal(to_float(f))); }
vm_obj float_sign(vm_obj const & f) {return mk_vm_bool(signbit(to_float(f))); }

vm_obj float_exponent(vm_obj const & f) {return mk_vm_int(ilogb(to_float(f))); }

vm_obj float_qNaN() {return mk_vm_float(std::numeric_limits<float>::quiet_NaN()); }
vm_obj float_sNaN() {return mk_vm_float(std::numeric_limits<float>::signaling_NaN()); }

vm_obj float_add(vm_obj const & a1, vm_obj const & a2) {return mk_vm_float(to_float(a1) + to_float(a2));}
vm_obj float_sub(vm_obj const & a1, vm_obj const & a2) {return mk_vm_float(to_float(a1) - to_float(a2));}
vm_obj float_neg(vm_obj const & a1) {return mk_vm_float(-to_float(a1));}
vm_obj float_mul(vm_obj const & a1, vm_obj const & a2) {return mk_vm_float(to_float(a1) * to_float(a2));}
vm_obj float_div(vm_obj const & a1, vm_obj const & a2) {return mk_vm_float(to_float(a1) / to_float(a2));}

vm_obj float_pow(vm_obj const & a1, vm_obj const & a2) {return mk_vm_float(pow(to_float(a1), to_float(a2)));}
vm_obj float_sqrt(vm_obj const & a1) {return mk_vm_float(sqrt(to_float(a1)));}
vm_obj float_exp(vm_obj const & e1) { return mk_vm_float(exp(to_float(e1)));}
vm_obj float_log(vm_obj const & e1) { return mk_vm_float(log(to_float(e1)));}

vm_obj float_pi() {return mk_vm_float(3.141592653589793);}

vm_obj float_sin(vm_obj const & e1) { return mk_vm_float(sin(to_float(e1)));}
vm_obj float_cos(vm_obj const & e1) { return mk_vm_float(cos(to_float(e1)));}
vm_obj float_tan(vm_obj const & e1) { return mk_vm_float(tan(to_float(e1)));}

vm_obj float_asin(vm_obj const & e1) { return mk_vm_float(asin(to_float(e1)));}
vm_obj float_acos(vm_obj const & e1) { return mk_vm_float(acos(to_float(e1)));}
vm_obj float_atan(vm_obj const & e1) { return mk_vm_float(atan(to_float(e1)));}
vm_obj float_atan2(vm_obj const & e1, vm_obj const & e2) { return mk_vm_float(atan2(to_float(e1), to_float(e2)));}

vm_obj float_sinh(vm_obj const & e1) { return mk_vm_float(sinh(to_float(e1)));}
vm_obj float_cosh(vm_obj const & e1) { return mk_vm_float(cosh(to_float(e1)));}
vm_obj float_tanh(vm_obj const & e1) { return mk_vm_float(tanh(to_float(e1)));}

vm_obj float_abs(vm_obj const & a1) {return mk_vm_float(abs(to_float(a1)));}
vm_obj float_ceil(vm_obj const & e1) { return mk_vm_float(ceil(to_float(e1)));}
vm_obj float_floor(vm_obj const & e1) { return mk_vm_float(floor(to_float(e1)));}

vm_obj float_lt(vm_obj const & a1, vm_obj const & a2) {return mk_vm_bool(to_float(a1) < to_float(a2));}
vm_obj float_dec_eq(vm_obj const & a1, vm_obj const & a2) {return mk_vm_bool(to_float(a1) == to_float(a2));}

vm_obj float_of_nat(vm_obj const & a) {
    //[TODO] check that the nat isn't too big to fit in an unsigned
    return mk_vm_float((float)(to_unsigned(a)));
}
vm_obj float_of_int(vm_obj const & i) {
    return mk_vm_float(to_int(i));
}

vm_obj float_repr(vm_obj const & a) {
    std::ostringstream out;
    float f = to_float(a);
    out << f;
    return to_obj(out.str());
}

void initialize_vm_float() {

    DECLARE_VM_BUILTIN(name({"native","float","specification","radix"}), spec_radix);
    DECLARE_VM_BUILTIN(name({"native","float","specification","precision"}), spec_precision);
    DECLARE_VM_BUILTIN(name({"native","float","specification","emax"}), spec_emax);
    DECLARE_VM_BUILTIN(name({"native","float","specification","emin"}), spec_emin);

    DECLARE_VM_BUILTIN(name({"native","float","epsilon"}), float_epsilon);
    DECLARE_VM_BUILTIN(name({"native","float","infinity"}), float_infinity);
    DECLARE_VM_BUILTIN(name({"native","float","is_infinite"}), float_is_infinite);
    DECLARE_VM_BUILTIN(name({"native","float","is_finite"}), float_is_finite);
    DECLARE_VM_BUILTIN(name({"native","float","is_nan"}), float_is_nan);
    DECLARE_VM_BUILTIN(name({"native","float","is_normal"}), float_is_normal);
    DECLARE_VM_BUILTIN(name({"native","float","sign"}), float_sign);

    DECLARE_VM_BUILTIN(name({"native","float","exponent"}), float_exponent);

    DECLARE_VM_BUILTIN(name({"native","float","qNaN"}), float_qNaN);
    DECLARE_VM_BUILTIN(name({"native","float","sNaN"}), float_sNaN);
    // DECLARE_VM_BUILTIN(name({"native","float","is_qNaN"}), _);
    // DECLARE_VM_BUILTIN(name({"native","float","sNaN"}), _);
    // DECLARE_VM_BUILTIN(name({"native","float","is_sNaN"}), _);

    // DECLARE_VM_BUILTIN(name({"native","float","sign"}), _);
    // DECLARE_VM_BUILTIN(name({"native","float","exponent"}), _);
    // DECLARE_VM_BUILTIN(name({"native","float","mantissa"}), _);


    DECLARE_VM_BUILTIN(name({"native","float","add"}), float_add);
    DECLARE_VM_BUILTIN(name({"native","float","sub"}), float_sub);
    DECLARE_VM_BUILTIN(name({"native","float","neg"}), float_neg);
    DECLARE_VM_BUILTIN(name({"native","float","mul"}), float_mul);
    DECLARE_VM_BUILTIN(name({"native","float","div"}), float_div);

    DECLARE_VM_BUILTIN(name({"native","float","pow"}), float_pow);
    DECLARE_VM_BUILTIN(name({"native","float","sqrt"}), float_sqrt);
    DECLARE_VM_BUILTIN(name({"native","float","exp"}), float_exp);
    DECLARE_VM_BUILTIN(name({"native","float","log"}), float_log);

    DECLARE_VM_BUILTIN(name({"native","float","pi"}), float_pi);

    DECLARE_VM_BUILTIN(name({"native","float","sin"}), float_sin);
    DECLARE_VM_BUILTIN(name({"native","float","cos"}), float_cos);
    DECLARE_VM_BUILTIN(name({"native","float","tan"}), float_tan);

    DECLARE_VM_BUILTIN(name({"native","float","asin"}), float_asin);
    DECLARE_VM_BUILTIN(name({"native","float","acos"}), float_acos);
    DECLARE_VM_BUILTIN(name({"native","float","atan"}), float_atan);
    DECLARE_VM_BUILTIN(name({"native","float","atan2"}), float_atan2);

    DECLARE_VM_BUILTIN(name({"native","float","sinh"}), float_sinh);
    DECLARE_VM_BUILTIN(name({"native","float","cosh"}), float_cosh);
    DECLARE_VM_BUILTIN(name({"native","float","tanh"}), float_tanh);

    DECLARE_VM_BUILTIN(name({"native","float","abs"}), float_abs);
    DECLARE_VM_BUILTIN(name({"native","float","ceil"}), float_ceil);
    DECLARE_VM_BUILTIN(name({"native","float","floor"}), float_floor);

    DECLARE_VM_BUILTIN(name({"native","float","lt"}), float_lt);
    DECLARE_VM_BUILTIN(name({"native","float","dec_eq"}), float_dec_eq);

    DECLARE_VM_BUILTIN(name({"native","float","of_nat"}), float_of_nat);
    DECLARE_VM_BUILTIN(name({"native","float","of_int"}), float_of_int);

    DECLARE_VM_BUILTIN(name({"native","float","to_repr"}), float_repr);
}
void finalize_vm_float() {
}
}