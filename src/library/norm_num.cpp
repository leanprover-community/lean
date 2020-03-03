/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
*/
#include "library/trace.h"
#include "library/norm_num.h"
#include "library/util.h"
#include "library/constants.h"
#include "library/comp_val.h"

namespace lean {
bool norm_num_context::is_numeral(expr const & e) const {
    return is_num(e);
}

bool norm_num_context::is_nat_const(expr const & e) const {
    return is_constant(e) && const_name(e) == get_nat_name();
}

bool norm_num_context::is_neg_app(expr const & e) const {
    return is_const_app(e, get_has_neg_neg_name(), 3);
}

bool norm_num_context::is_div(expr const & e) const {
    return is_const_app(e, get_has_div_div_name(), 4);
}

expr norm_num_context::mk_const(name const & n) {
    return mk_constant(n, m_ainst.get_levels());
}

expr norm_num_context::mk_cong(expr const & op, expr const & type, expr const & a,
                               expr const & b, expr const & eq) {
    return mk_app({mk_const(get_norm_num_mk_cong_name()), type, op, a, b, eq});
}

// returns <t, p> such that p is a proof that lhs + rhs = t.
pair<expr, expr> norm_num_context::mk_norm_add(expr const & lhs, expr const & rhs) {
    buffer<expr> args_lhs;
    buffer<expr> args_rhs;
    expr lhs_head = get_app_args (lhs, args_lhs);
    expr rhs_head = get_app_args (rhs, args_rhs);
    if (!is_constant(lhs_head) || !is_constant(rhs_head)) {
        throw exception("cannot take norm_add of nonconstant");
    }
    auto type = args_lhs[0];
    auto typec = args_lhs[1];
    expr rv;
    expr prf;
    if (is_bit0(lhs) && is_bit0(rhs)) { // typec is has_add
        auto p = mk_norm_add(args_lhs[2], args_rhs[2]);
        rv = mk_app(lhs_head, type, typec, p.first);
        prf = mk_app({mk_const(get_norm_num_bit0_add_bit0_helper_name()), type, mk_add_comm(),
                    args_lhs[2], args_rhs[2], p.first, p.second});
    } else if (is_bit0(lhs) && is_bit1(rhs)) {
        auto p = mk_norm_add(args_lhs[2], args_rhs[3]);
        rv = mk_app({rhs_head, type, args_rhs[1], args_rhs[2], p.first});
        prf = mk_app({mk_const(get_norm_num_bit0_add_bit1_helper_name()), type, mk_add_comm(), args_rhs[1],
                    args_lhs[2], args_rhs[3], p.first, p.second});
    } else if (is_bit0(lhs) && is_one(rhs)) {
        rv  = mk_bit1(args_lhs[2]);
        prf = mk_app({mk_const(get_norm_num_bit0_add_one_name()), type, typec, args_rhs[1], args_lhs[2]});
    } else if (is_bit1(lhs) && is_bit0(rhs)) { // typec is has_one
        auto p = mk_norm_add(args_lhs[3], args_rhs[2]);
        rv  = mk_app(lhs_head, type, typec, args_lhs[2], p.first);
        prf = mk_app({mk_const(get_norm_num_bit1_add_bit0_helper_name()), type, mk_add_comm(), typec,
                    args_lhs[3], args_rhs[2], p.first, p.second});
    } else if (is_bit1(lhs) && is_bit1(rhs)) { // typec is has_one
        auto add_ts = mk_norm_add(args_lhs[3], args_rhs[3]);
        expr add1   = mk_app({mk_const(get_norm_num_add1_name()), type, args_lhs[2], typec, add_ts.first});
        auto p = mk_norm_add1(add1);
        rv  = mk_bit0(p.first);
        prf = mk_app({mk_const(get_norm_num_bit1_add_bit1_helper_name()), type, mk_add_comm(), typec,
                    args_lhs[3], args_rhs[3], add_ts.first, p.first, add_ts.second, p.second});
    } else if (is_bit1(lhs) && is_one(rhs)) { // typec is has_one
        expr add1 = mk_app({mk_const(get_norm_num_add1_name()), type, args_lhs[2], typec, lhs});
        auto p = mk_norm_add1(add1);
        rv = p.first;
        prf = mk_app({mk_const(get_norm_num_bit1_add_one_helper_name()), type, args_lhs[2], typec,
                    args_lhs[3], p.first, p.second});
    } else if (is_one(lhs) && is_bit0(rhs)) { // typec is has_one
        rv  = mk_bit1(args_rhs[2]);
        prf = mk_app({mk_const(get_norm_num_one_add_bit0_name()), type, mk_add_comm(), typec, args_rhs[2]});
    } else if (is_one(lhs) && is_bit1(rhs)) { // typec is has_one
        expr add1 = mk_app({mk_const(get_norm_num_add1_name()), type, args_rhs[2], args_rhs[1], rhs});
        auto p = mk_norm_add1(add1);
        rv  = p.first;
        prf = mk_app({mk_const(get_norm_num_one_add_bit1_helper_name()), type, mk_add_comm(), typec,
                    args_rhs[3], p.first, p.second});
    } else if (is_one(lhs) && is_one(rhs)) {
        rv  = mk_bit0(lhs);
        prf = mk_app({mk_const(get_norm_num_one_add_one_name()), type, mk_has_add(), typec});
    } else if (is_zero(lhs)) {
        rv  = rhs;
        prf = mk_app({mk_const(get_norm_num_bin_zero_add_name()), type, mk_add_monoid(), rhs});
    } else if (is_zero(rhs)) {
        rv  = lhs;
        prf = mk_app({mk_const(get_norm_num_bin_add_zero_name()), type, mk_add_monoid(), lhs});
    } else {
        throw exception("mk_norm_add got malformed args");
    }
    return pair<expr, expr>(rv, prf);
}

pair<expr, expr> norm_num_context::mk_norm_add1(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    expr p = args[3];
    buffer<expr> ne_args;
    expr ne = get_app_args(p, ne_args);
    expr rv;
    expr prf;
    // args[1] = has_add, args[2] = has_one
    if (is_bit0(p)) {
        auto has_one = args[2];
        rv  = mk_bit1(ne_args[2]);
        prf = mk_app({mk_const(get_norm_num_add1_bit0_name()), args[0], args[1], args[2], ne_args[2]});
    } else if (is_bit1(p)) { // ne_args : has_one, has_add
        auto np = mk_norm_add1(mk_app({mk_const(get_norm_num_add1_name()), args[0], args[1], args[2], ne_args[3]}));
        rv  = mk_bit0(np.first);
        prf = mk_app({mk_const(get_norm_num_add1_bit1_helper_name()), args[0], mk_add_comm(),
                    args[2], ne_args[3], np.first, np.second});
    } else if (is_zero(p)) {
        rv  = mk_one();
        prf = mk_app({mk_const(get_norm_num_add1_zero_name()), args[0], mk_add_monoid(), args[2]});
    } else if (is_one(p)) {
        rv  = mk_bit0(mk_one());
        prf = mk_app({mk_const(get_norm_num_add1_one_name()), args[0], args[1], args[2]});
    } else {
        throw exception("malformed add1");
    }
    return pair<expr, expr>(rv, prf);
}

pair<expr, expr> norm_num_context::mk_norm_mul(expr const & lhs, expr const & rhs) {
    buffer<expr> args_lhs;
    buffer<expr> args_rhs;
    expr lhs_head = get_app_args (lhs, args_lhs);
    expr rhs_head = get_app_args (rhs, args_rhs);
    if (!is_constant(lhs_head) || !is_constant(rhs_head)) {
        throw exception("cannot take norm_add of nonconstant");
    }
    auto type = args_rhs[0];
    auto typec = args_rhs[1];
    expr rv;
    expr prf;
    if (is_zero(rhs)) {
        rv  = rhs;
        prf = mk_app({mk_const(get_mul_zero_name()), type, mk_mul_zero_class(), lhs});
    } else if (is_zero(lhs)) {
        rv  = lhs;
        prf = mk_app({mk_const(get_zero_mul_name()), type, mk_mul_zero_class(), rhs});
    } else if (is_one(rhs)) {
        rv  = lhs;
        prf = mk_app({mk_const(get_mul_one_name()), type, mk_monoid(), lhs});
    } else if (is_bit0(rhs)) {
        auto mtp = mk_norm_mul(lhs, args_rhs[2]);
        rv  = mk_app({rhs_head, type, typec, mtp.first});
        prf = mk_app({mk_const(get_norm_num_mul_bit0_helper_name()), type, mk_distrib(), lhs,
                    args_rhs[2], mtp.first, mtp.second});
    } else if (is_bit1(rhs)) {
        auto mtp = mk_norm_mul(lhs, args_rhs[3]);
        auto atp = mk_norm_add(mk_bit0(mtp.first), lhs);
        rv  = atp.first;
        prf = mk_app({mk_const(get_norm_num_mul_bit1_helper_name()), type, mk_semiring(), lhs, args_rhs[3],
                    mtp.first, atp.first, mtp.second, atp.second});
    } else {
        throw exception("mk_norm_mul got malformed args");
    }
    return pair<expr, expr>(rv, prf);
}

optional<mpq> norm_num_context::to_mpq(expr const & e) {
    auto v = to_num(e);
    if (v) {
        return optional<mpq>(mpq(*v));
    } else {
        return optional<mpq>();
    }
}

mpq norm_num_context::mpq_of_expr(expr const & e) {
    if (auto r = m_ainst.eval(e))
        return *r;
    else
        throw exception("failed to evaluate arithmetic expression");
}

pair<expr, expr> norm_num_context::get_type_and_arg_of_neg(expr const & e) {
    lean_assert(is_neg_app(e));
    buffer<expr> args;
    expr f = get_app_args(e, args);
    return pair<expr, expr>(args[0], args[2]);
}

// returns a proof that s_lhs + s_rhs = rhs, where all are negated numerals
expr norm_num_context::mk_norm_eq_neg_add_neg(expr const & s_lhs, expr const & s_rhs, expr const & rhs) {
    lean_assert(is_neg_app(s_lhs));
    lean_assert(is_neg_app(s_rhs));
    lean_assert(is_neg_app(rhs));
    auto s_lhs_v = get_type_and_arg_of_neg(s_lhs).second;
    auto s_rhs_v = get_type_and_arg_of_neg(s_rhs).second;
    auto rhs_v = get_type_and_arg_of_neg(rhs);
    expr type = rhs_v.first;
    auto sum_pr = mk_norm(mk_add(s_lhs_v, s_rhs_v)).second;
    return mk_app({mk_const(get_norm_num_neg_add_neg_helper_name()), type, mk_add_comm_group(),
                s_lhs_v, s_rhs_v, rhs_v.second, sum_pr});
}

expr norm_num_context::mk_norm_eq_neg_add_pos(expr const & s_lhs, expr const & s_rhs, expr const & rhs) {
    lean_assert(is_neg_app(s_lhs));
    lean_assert(!is_neg_app(s_rhs));
    auto s_lhs_v = get_type_and_arg_of_neg(s_lhs);
    expr type = s_lhs_v.first;
    if (is_neg_app(rhs)) {
        auto rhs_v = get_type_and_arg_of_neg(rhs).second;
        auto sum_pr = mk_norm(mk_add(s_rhs, rhs_v)).second;
        return mk_app({mk_const(get_norm_num_neg_add_pos_helper1_name()), type, mk_add_comm_group(),
                    s_lhs_v.second, s_rhs, rhs_v, sum_pr});
    } else {
        auto sum_pr = mk_norm(mk_add(s_lhs_v.second, rhs)).second;
        return mk_app({mk_const(get_norm_num_neg_add_pos_helper2_name()), type, mk_add_comm_group(),
                    s_lhs_v.second, s_rhs, rhs, sum_pr});
    }
}

expr norm_num_context::mk_norm_eq_pos_add_neg(expr const & s_lhs, expr const & s_rhs, expr const & rhs) {
    lean_assert(is_neg_app(s_rhs));
    lean_assert(!is_neg_app(s_lhs));
    expr prf = mk_norm_eq_neg_add_pos(s_rhs, s_lhs, rhs);
    expr type = get_type_and_arg_of_neg(s_rhs).first;
    return mk_app({mk_const(get_norm_num_pos_add_neg_helper_name()), type, mk_add_comm_group(), s_lhs,
                s_rhs, rhs, prf});
}

// returns a proof that s_lhs + s_rhs = rhs, where all are nonneg normalized numerals
expr norm_num_context::mk_norm_eq_pos_add_pos(expr const & s_lhs, expr const & s_rhs, expr const & DEBUG_CODE(rhs)) {
    lean_assert(!is_neg_app(s_lhs));
    lean_assert(!is_neg_app(s_rhs));
    lean_assert(!is_neg_app(rhs));
    auto p = mk_norm_add(s_lhs, s_rhs);
    lean_assert(to_num(rhs) == to_num(p.first));
    return p.second;
}

expr norm_num_context::mk_norm_eq_neg_mul_neg(expr const & s_lhs, expr const & s_rhs, expr const & rhs) {
    lean_assert(is_neg_app(s_lhs));
    lean_assert(is_neg_app(s_rhs));
    lean_assert(!is_neg_app(rhs));
    auto s_lhs_v = get_type_and_arg_of_neg(s_lhs).second;
    expr s_rhs_v, type;
    std::tie(type, s_rhs_v) = get_type_and_arg_of_neg(s_rhs);
    auto prod_pr = mk_norm(mk_mul(s_lhs_v, s_rhs_v));
    lean_assert(to_num(rhs) == to_num(prod_pr.first));
    return mk_app({mk_const(get_norm_num_neg_mul_neg_helper_name()), type, mk_ring(), s_lhs_v,
                s_rhs_v, rhs, prod_pr.second});
}

expr norm_num_context::mk_norm_eq_neg_mul_pos(expr const & s_lhs, expr const & s_rhs, expr const & rhs) {
    lean_assert(is_neg_app(s_lhs));
    lean_assert(!is_neg_app(s_rhs));
    lean_assert(is_neg_app(rhs));
    expr s_lhs_v, type;
    std::tie(type, s_lhs_v) = get_type_and_arg_of_neg(s_lhs);
    auto rhs_v = get_type_and_arg_of_neg(rhs).second;
    auto prod_pr = mk_norm(mk_mul(s_lhs_v, s_rhs));
    return mk_app({mk_const(get_norm_num_neg_mul_pos_helper_name()), type, mk_ring(), s_lhs_v, s_rhs,
                rhs_v, prod_pr.second});
}

expr norm_num_context::mk_norm_eq_pos_mul_neg(expr const & s_lhs, expr const & s_rhs, expr const & rhs) {
    lean_assert(!is_neg_app(s_lhs));
    lean_assert(is_neg_app(s_rhs));
    lean_assert(is_neg_app(rhs));
    expr s_rhs_v, type;
    std::tie(type, s_rhs_v) = get_type_and_arg_of_neg(s_rhs);
    auto rhs_v = get_type_and_arg_of_neg(rhs).second;
    auto prod_pr = mk_norm(mk_mul(s_lhs, s_rhs_v));
    return mk_app({mk_const(get_norm_num_pos_mul_neg_helper_name()), type, mk_ring(), s_lhs, s_rhs_v,
                rhs_v, prod_pr.second});
}

// returns a proof that s_lhs + s_rhs = rhs, where all are nonneg normalized numerals
expr norm_num_context::mk_norm_eq_pos_mul_pos(expr const & s_lhs, expr const & s_rhs, expr const & DEBUG_CODE(rhs)) {
    lean_assert(!is_neg_app(s_lhs));
    lean_assert(!is_neg_app(s_rhs));
    lean_assert(!is_neg_app(rhs));
    auto p = mk_norm_mul(s_lhs, s_rhs);
    lean_assert(to_num(rhs) == to_num(p.first));
    return p.second;
}

// s_lhs is div. returns proof that s_lhs + s_rhs = rhs
expr norm_num_context::mk_norm_div_add(expr const & s_lhs, expr const & s_rhs, expr const & rhs) {
    buffer<expr> s_lhs_args;
    get_app_args(s_lhs, s_lhs_args);
    expr type = s_lhs_args[0];
    expr num = s_lhs_args[2], den = s_lhs_args[3];
    expr new_lhs = mk_add(num, mk_mul(s_rhs, den));
    auto npr_l = mk_norm(new_lhs);
    auto npr_r = mk_norm(mk_mul(rhs, den));
    lean_assert(to_mpq(npr_l.first) == to_mpq(npr_r.first));
    expr den_neq_zero = mk_nonzero_prf(den);
    return mk_app({mk_const(get_norm_num_div_add_helper_name()), type, mk_field(), num, den, s_rhs, rhs,
                npr_l.first, den_neq_zero, npr_l.second, npr_r.second});
}

// s_rhs is div. returns proof that s_lhs + s_rhs = rhs
expr norm_num_context::mk_norm_add_div(expr const & s_lhs, expr const & s_rhs, expr const & rhs) {
    buffer<expr> s_rhs_args;
    get_app_args(s_rhs, s_rhs_args);
    expr type = s_rhs_args[0];
    expr num = s_rhs_args[2], den = s_rhs_args[3];
    expr new_lhs = mk_add(mk_mul(den, s_lhs), num);
    auto npr_l = mk_norm(new_lhs);
    auto npr_r = mk_norm(mk_mul(den, rhs));
    lean_assert(to_mpq(npr_l.first) == to_mpq(npr_r.first));
    expr den_neq_zero = mk_nonzero_prf(den);
    return mk_app({mk_const(get_norm_num_add_div_helper_name()), type, mk_field(), num, den, s_lhs, rhs,
                npr_l.first, den_neq_zero, npr_l.second, npr_r.second});
}

// if e is a numeral or a negation of a numeral or division, returns proof that e != 0
expr norm_num_context::mk_nonzero_prf(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    if (const_name(f) == get_has_neg_neg_name()) {
        return mk_app({mk_const(get_norm_num_nonzero_of_neg_helper_name()), args[0], mk_lin_ord_ring(),
                    args[2], mk_nonzero_prf(args[2])});
    } else if (const_name(f) == get_has_div_div_name()) {
        expr num_pr = mk_nonzero_prf(args[2]), den_pr = mk_nonzero_prf(args[3]);
        return mk_app({mk_const(get_norm_num_nonzero_of_div_helper_name()), args[0], mk_field(), args[2],
                    args[3], num_pr, den_pr});
    } else {
        return mk_app({mk_const(get_norm_num_nonzero_of_pos_helper_name()), args[0], mk_lin_ord_semiring(),
                    e, mk_pos_prf(e)});
    }
}

// if e is a numeral, makes a proof that e > 0
expr norm_num_context::mk_pos_prf(expr const & e) {
    buffer<expr> args;
    get_app_args(e, args);
    expr type = args[0];
    expr prf;
    if (is_bit0(e)) {
        prf = mk_pos_prf(args[2]);
        return mk_app({mk_const(get_norm_num_pos_bit0_helper_name()), type, mk_lin_ord_semiring(), args[2], prf});
    } else if (is_bit1(e)) {
        prf = mk_nonneg_prf(args[3]);
        return mk_app({mk_const(get_norm_num_pos_bit1_helper_name()), type, mk_lin_ord_semiring(), args[3], prf});
    } else if (is_one(e)) {
        return mk_app({mk_const(get_zero_lt_one_name()), type, mk_lin_ord_semiring()});
    } else {
        throw exception("mk_pos_proof called on zero or non_numeral");
    }
}

expr norm_num_context::mk_nonneg_prf(expr const & e) {
    buffer<expr> args;
    get_app_args(e, args);
    expr type = args[0];
    expr prf;
    if (is_bit0(e)) {
        prf = mk_nonneg_prf(args[2]);
        return mk_app({mk_const(get_norm_num_nonneg_bit0_helper_name()), type, mk_lin_ord_semiring(), args[2], prf});
    } else if (is_bit1(e)) {
        prf = mk_nonneg_prf(args[3]);
        return mk_app({mk_const(get_norm_num_nonneg_bit1_helper_name()), type, mk_lin_ord_semiring(), args[3], prf});
    } else if (is_one(e)) {
        return mk_app({mk_const(get_zero_le_one_name()), type, mk_lin_ord_semiring()});
    } else if (is_zero(e)) {
        return mk_app({mk_const(get_le_refl_name()), type, mk_partial_order(), mk_zero()});
    } else {
        throw exception("mk_nonneg_proof called on zero or non_numeral");
    }
}

// s_lhs is div. returns proof that s_lhs * s_rhs = rhs
expr norm_num_context::mk_norm_div_mul(expr const & s_lhs, expr const & s_rhs, expr const & rhs) {
    buffer<expr> args;
    get_app_args(s_lhs, args);
    expr type = args[0];
    expr new_num = mk_mul(args[2], s_rhs);
    auto prf = mk_norm(mk_div(new_num, args[3]));
    lean_assert(to_mpq(prf.first) == to_mpq(rhs));
    return mk_app({mk_const(get_norm_num_div_mul_helper_name()), type, mk_field(), args[2], args[3], s_rhs,
                rhs, prf.second});
}

expr norm_num_context::mk_norm_mul_div(expr const & s_lhs, expr const & s_rhs, expr const & rhs) {
    buffer<expr> args;
    get_app_args(s_rhs, args);
    expr type = args[0];
    expr new_num = mk_mul(s_lhs, args[2]);
    auto prf = mk_norm(mk_div(new_num, args[3]));
    lean_assert(to_mpq(prf.first) == to_mpq(rhs));
    expr den_ne_zero = mk_nonzero_prf(args[3]);
    return mk_app({mk_const(get_norm_num_mul_div_helper_name()), type, mk_field(), s_lhs, args[2], args[3],
                rhs, den_ne_zero, prf.second});
}

expr_pair norm_num_context::mk_norm_nat_sub(expr const & s_lhs, expr const & s_rhs) {
    auto norm_lhs = mk_norm(s_lhs);
    auto norm_rhs = mk_norm(s_rhs);
    mpq vall = mpq_of_expr(norm_lhs.first);
    mpq valr = mpq_of_expr(norm_rhs.first);
    if (valr > vall) {
        if (auto lt_pr = mk_nat_val_lt_proof(norm_lhs.first, norm_rhs.first)) {
            expr zeropr = mk_app({mk_constant(get_norm_num_sub_nat_zero_helper_name()),
                        s_lhs, s_rhs, norm_lhs.first, norm_rhs.first, norm_lhs.second, norm_rhs.second, *lt_pr});
            return expr_pair(mk_zero(), zeropr);
        } else {
            throw exception("mk_norm_nat_sub failed to make lt proof");
        }
    } else {
        expr e = mk_num(vall - valr);
        auto seq_pr = mk_norm(mk_add(e, norm_rhs.first));
        expr rpr = mk_app({mk_constant(get_norm_num_sub_nat_pos_helper_name()),
                    s_lhs, s_rhs, norm_lhs.first, norm_rhs.first, e, norm_lhs.second, norm_rhs.second, seq_pr.second});
        return expr_pair(e, rpr);
    }
}

pair<expr, expr> norm_num_context::mk_norm(expr const & e) {
    buffer<expr> args;
    expr f = get_app_args(e, args);
    if (!is_constant(f) || args.size() == 0) {
        throw exception("malformed argument to mk_norm");
    }
    expr type = args[0];
    m_ainst.set_type(type);
    if (is_numeral(e)) {
        expr prf = mk_eq_refl(m_ctx, e);
        return pair<expr, expr>(e, prf);
    }
    mpq val   = mpq_of_expr(e);
    expr nval = mk_num(val);

    if (const_name(f) == get_has_add_add_name() && args.size() == 4) {
        expr prf;
        auto lhs_p = mk_norm(args[2]);
        auto rhs_p = mk_norm(args[3]);
        if (is_neg_app(lhs_p.first)) {
            if (is_neg_app(rhs_p.first)) {
                prf = mk_norm_eq_neg_add_neg(lhs_p.first, rhs_p.first, nval);
            } else {
                prf = mk_norm_eq_neg_add_pos(lhs_p.first, rhs_p.first, nval);
            }
        } else {
            if (is_neg_app(rhs_p.first)) {
                prf = mk_norm_eq_pos_add_neg(lhs_p.first, rhs_p.first, nval);
            } else {
                if (is_div(lhs_p.first)) {
                    prf = mk_norm_div_add(lhs_p.first, rhs_p.first, nval);
                } else if (is_div(rhs_p.first)) {
                    prf = mk_norm_add_div(lhs_p.first, rhs_p.first, nval);
                } else {
                    prf = mk_norm_eq_pos_add_pos(lhs_p.first, rhs_p.first, nval);
                }
            }
        }
        expr rprf = mk_app({mk_const(get_norm_num_subst_into_sum_name()), type, mk_has_add(), args[2], args[3],
                    lhs_p.first, rhs_p.first, nval, lhs_p.second, rhs_p.second, prf});
        return pair<expr, expr>(nval, rprf);

    } else if (const_name(f) == get_has_sub_sub_name() && args.size() == 4) {
        if (is_nat_const(args[0])) {
            return mk_norm_nat_sub(args[2], args[3]);
        }
        expr sum = mk_add(args[2], mk_neg(args[3]));
        auto anprf = mk_norm(sum);
        expr rprf = mk_app({mk_const(get_norm_num_subst_into_subtr_name()), type, mk_add_group(), args[2],
            args[3], anprf.first, anprf.second});
        return expr_pair(nval, rprf);
    } else if (const_name(f) == get_has_neg_neg_name()  && args.size() == 3) {
        auto prf = mk_norm(args[2]);
        lean_assert(mpq_of_expr(prf.first) == neg(val));
        if (is_zero(prf.first)) {
            expr rprf = mk_app({mk_const(get_norm_num_neg_zero_helper_name()), type, mk_add_group(), args[2],
                        prf.second});
            return pair<expr, expr>(prf.first, rprf);
        }

        if (is_neg_app(nval)) {
            buffer<expr> nval_args;
            get_app_args(nval, nval_args);
            expr rprf = mk_cong(mk_app(f, args[0], args[1]), type, args[2],
                                nval_args[2], prf.second);
            return pair<expr, expr>(nval, rprf);
        } else {
            expr rprf = mk_app({mk_const(get_norm_num_neg_neg_helper_name()), type, mk_add_group(),
                        args[2], nval, prf.second});
            return pair<expr, expr>(nval, rprf);
        }
    } else if (const_name(f) == get_has_mul_mul_name() && args.size() == 4) {
        auto lhs_p = mk_norm(args[2]);
        auto rhs_p = mk_norm(args[3]);
        expr prf;
        if (is_div(lhs_p.first)) {
            prf = mk_norm_div_mul(lhs_p.first, rhs_p.first, nval);
        } else if (is_div(rhs_p.first)) {
            prf = mk_norm_mul_div(lhs_p.first, rhs_p.first, nval);
        } else if (is_zero(lhs_p.first) || is_zero(rhs_p.first)) {
            prf = mk_norm_mul(lhs_p.first, rhs_p.first).second;
        } else if (is_neg_app(lhs_p.first)) {
            if (is_neg_app(rhs_p.first)) {
                prf = mk_norm_eq_neg_mul_neg(lhs_p.first, rhs_p.first, nval);
            } else { // bad args passing here
                prf = mk_norm_eq_neg_mul_pos(lhs_p.first, rhs_p.first, nval);
            }
        } else {
            if (is_neg_app(rhs_p.first)) {
                prf = mk_norm_eq_pos_mul_neg(lhs_p.first, rhs_p.first, nval);
            } else {
                prf = mk_norm_eq_pos_mul_pos(lhs_p.first, rhs_p.first, nval);
            }
        }
        expr rprf = mk_app({mk_const(get_norm_num_subst_into_prod_name()), type, mk_has_mul(), args[2], args[3],
                          lhs_p.first, rhs_p.first, nval, lhs_p.second, rhs_p.second, prf});
        return pair<expr, expr>(nval, rprf);
    } else if (const_name(f) == get_has_div_div_name() && args.size() == 4) {
        auto lhs_p = mk_norm(args[2]);
        auto rhs_p = mk_norm(args[3]);
        expr prf;
        if (is_div(nval)) {
            buffer<expr> nval_args;
            get_app_args(nval, nval_args);
            expr nval_num = nval_args[2], nval_den = nval_args[3];
            auto lhs_mul = mk_norm(mk_mul(lhs_p.first, nval_den));
            auto rhs_mul = mk_norm(mk_mul(nval_num, rhs_p.first));
            expr den_nonzero = mk_nonzero_prf(rhs_p.first);
            expr nval_den_nonzero = mk_nonzero_prf(nval_den);
            prf = mk_app({mk_const(get_norm_num_div_eq_div_helper_name()), type, mk_field(),
                        lhs_p.first, rhs_p.first, nval_num, nval_den, lhs_mul.first,
                        lhs_mul.second, rhs_mul.second, den_nonzero, nval_den_nonzero});
        } else {
            auto prod = mk_norm(mk_mul(nval, rhs_p.first));
            auto val1 = to_mpq(prod.first), val2 = to_mpq(lhs_p.first);
            if (val1 && val2) {
                lean_assert(*val1 == *val2);
            }
            expr den_nonzero = mk_nonzero_prf(rhs_p.first);
            prf = mk_app({mk_const(get_norm_num_div_helper_name()), type, mk_field(),
                        lhs_p.first, rhs_p.first, nval, den_nonzero, prod.second});
        }
        expr rprf = mk_app({mk_const(get_norm_num_subst_into_div_name()), type, mk_has_div(),
                    lhs_p.first, rhs_p.first, args[2], args[3], nval, prf,
                    lhs_p.second, rhs_p.second});
        return pair<expr, expr>(nval, rprf);
    } else if (const_name(f) == get_bit0_name() && args.size() == 3) {
        lean_assert(is_bit0(nval));
        buffer<expr> nval_args;
        get_app_args(nval, nval_args);
        auto prf = mk_norm(args[2]);
        auto rprf = mk_cong(mk_app(f, args[0], args[1]), type, args[2], nval_args[2], prf.second);
        return pair<expr, expr>(nval, rprf);
    } else if (const_name(f) == get_bit1_name() && args.size() == 4) {
        lean_assert(is_bit1(nval));
        buffer<expr> nval_args;
        get_app_args(nval, nval_args);
        auto prf = mk_norm(args[3]);
        auto rprf = mk_cong(mk_app(f, args[0], args[1], args[2]), type, args[3],
                            nval_args[3], prf.second);
        return pair<expr, expr>(nval, rprf);
    } else if ((const_name(f) == get_has_zero_zero_name() || const_name(f) == get_has_one_one_name())
               && args.size() == 2) {
        return pair<expr, expr>(e, mk_eq_refl(m_ctx, e));
    } else {
        throw exception("mk_norm found unrecognized combo ");
    }
}
}
