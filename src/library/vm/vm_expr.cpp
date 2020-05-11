/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <iostream>
#include "kernel/expr.h"
#include "kernel/free_vars.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "library/locals.h"
#include "library/sorry.h"
#include "library/util.h"
#include "library/expr_lt.h"
#include "library/deep_copy.h"
#include "library/comp_val.h"
#include "library/choice.h"
#include "library/annotation.h"
#include "library/quote.h"
#include "library/string.h"
#include "library/vm/vm.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_format.h"
#include "library/vm/vm_options.h"
#include "library/vm/vm_option.h"
#include "library/vm/vm_level.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_pos_info.h"
#include "library/vm/vm_rb_map.h"
#include "library/compiler/simp_inductive.h"
#include "library/compiler/nat_value.h"
#include "library/delayed_abstraction.h"

namespace lean {
struct vm_macro_definition : public vm_external {
    macro_definition m_val;
    vm_macro_definition(macro_definition const & v):m_val(v) {}
    virtual ~vm_macro_definition() {}
    virtual void dealloc() override {
        this->~vm_macro_definition(); get_vm_allocator().deallocate(sizeof(vm_macro_definition), this);
    }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_macro_definition(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_macro_definition))) vm_macro_definition(m_val); }
};

macro_definition const & to_macro_definition(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_macro_definition*>(to_external(o)));
    return static_cast<vm_macro_definition*>(to_external(o))->m_val;
}

vm_obj to_obj(macro_definition const & d) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_macro_definition))) vm_macro_definition(d));
}

struct vm_expr : public vm_external {
    expr m_val;
    vm_expr(expr const & v):m_val(v) {}
    virtual ~vm_expr() {}
    virtual void dealloc() override { this->~vm_expr(); get_vm_allocator().deallocate(sizeof(vm_expr), this); }
    virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_expr(m_val); }
    virtual vm_external * clone(vm_clone_fn const &) override { return new (get_vm_allocator().allocate(sizeof(vm_expr))) vm_expr(m_val); }
};

bool is_expr(vm_obj const & o) {
    return is_external(o) && dynamic_cast<vm_expr*>(to_external(o));
}

expr const & to_expr(vm_obj const & o) {
    lean_vm_check(dynamic_cast<vm_expr*>(to_external(o)));
    return static_cast<vm_expr*>(to_external(o))->m_val;
}

vm_obj to_obj(expr const & e) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_expr))) vm_expr(e));
}

vm_obj to_obj(optional<expr> const & e) {
    return e ? mk_vm_some(to_obj(*e)) : mk_vm_none();
}

binder_info to_binder_info(vm_obj const & o) {
    lean_assert(is_simple(o));
    /*
      inductive binder_info :=
      | default | implicit | strict_implicit | inst_implicit | aux_decl
    */
    switch (cidx(o)) {
    case 0:  return binder_info();
    case 1:  return mk_implicit_binder_info();
    case 2:  return mk_strict_implicit_binder_info();
    case 3:  return mk_inst_implicit_binder_info();
    default: return mk_rec_info(true);
    }
}

vm_obj to_obj(binder_info const & bi) {
    if (bi.is_implicit())
        return mk_vm_simple(1);
    else if (bi.is_strict_implicit())
        return mk_vm_simple(2);
    else if (bi.is_inst_implicit())
        return mk_vm_simple(3);
    else if (bi.is_rec())
        return mk_vm_simple(4);
    else
        return mk_vm_simple(0);
}

// The expr_var_intro function has an _intro suffix so that it doesn't clash
// with the expr_var class. This confuses GDB's python interface. The other
// introduction rules have the suffix for the same reason.

vm_obj expr_var_intro(vm_obj const &, vm_obj const & n) {
    return to_obj(mk_var(to_unsigned(n)));
}

vm_obj expr_sort_intro(vm_obj const &, vm_obj const & l) {
    return to_obj(mk_sort(to_level(l)));
}

vm_obj expr_const_intro(vm_obj const &, vm_obj const & n, vm_obj const & ls) {
    return to_obj(mk_constant(to_name(n), to_list_level(ls)));
}

vm_obj expr_mvar_intro(vm_obj const &, vm_obj const & n, vm_obj const & pp_n, vm_obj const & t) {
    return to_obj(mk_metavar(to_name(n), to_name(pp_n), to_expr(t)));
}

vm_obj expr_local_const_intro(vm_obj const &, vm_obj const & n, vm_obj const & ppn, vm_obj const & bi, vm_obj const & t) {
    return to_obj(mk_local(to_name(n), to_name(ppn), to_expr(t), to_binder_info(bi)));
}

vm_obj expr_app_intro(vm_obj const &, vm_obj const & f, vm_obj const & a) {
    return to_obj(mk_app(to_expr(f), to_expr(a)));
}

vm_obj expr_lam_intro(vm_obj const &, vm_obj const & n, vm_obj const & bi, vm_obj const & t, vm_obj const & b) {
    return to_obj(mk_lambda(to_name(n), to_expr(t), to_expr(b), to_binder_info(bi)));
}

vm_obj expr_pi_intro(vm_obj const &, vm_obj const & n, vm_obj const & bi, vm_obj const & t, vm_obj const & b) {
    return to_obj(mk_pi(to_name(n), to_expr(t), to_expr(b), to_binder_info(bi)));
}

vm_obj expr_elet_intro(vm_obj const &, vm_obj const & n, vm_obj const & t, vm_obj const & v, vm_obj const & b) {
    return to_obj(mk_let(to_name(n), to_expr(t), to_expr(v), to_expr(b)));
}

vm_obj expr_macro_intro(vm_obj const &, vm_obj const & d, vm_obj const & es) {
    buffer<expr> args;
    to_buffer_expr(es, args);
    return to_obj(mk_macro(to_macro_definition(d), args.size(), args.data()));
}

vm_obj expr_macro_def_name(vm_obj const & d) {
    return to_obj(to_macro_definition(d).get_name());
}

unsigned expr_cases_on(vm_obj const & o, buffer<vm_obj> & data) {
    expr const & e = to_expr(o);
    switch (e.kind()) {
    case expr_kind::Var:
        data.push_back(mk_vm_nat(var_idx(e)));
        break;
    case expr_kind::Sort:
        data.push_back(to_obj(sort_level(e)));
        break;
    case expr_kind::Constant:
        data.push_back(to_obj(const_name(e)));
        data.push_back(to_obj(const_levels(e)));
        break;
    case expr_kind::Meta:
        data.push_back(to_obj(mlocal_name(e)));
        data.push_back(to_obj(mlocal_pp_name(e)));
        data.push_back(to_obj(mlocal_type(e)));
        break;
    case expr_kind::Local:
        data.push_back(to_obj(mlocal_name(e)));
        data.push_back(to_obj(mlocal_pp_name(e)));
        data.push_back(to_obj(local_info(e)));
        data.push_back(to_obj(mlocal_type(e)));
        break;
    case expr_kind::App:
        data.push_back(to_obj(app_fn(e)));
        data.push_back(to_obj(app_arg(e)));
        break;
    case expr_kind::Lambda:
    case expr_kind::Pi:
        data.push_back(to_obj(binding_name(e)));
        data.push_back(to_obj(binding_info(e)));
        data.push_back(to_obj(binding_domain(e)));
        data.push_back(to_obj(binding_body(e)));
        break;
    case expr_kind::Let:
        data.push_back(to_obj(let_name(e)));
        data.push_back(to_obj(let_type(e)));
        data.push_back(to_obj(let_value(e)));
        data.push_back(to_obj(let_body(e)));
        break;
    case expr_kind::Macro:
        data.push_back(to_obj(macro_def(e)));
        buffer<expr> args;
        args.append(macro_num_args(e), macro_args(e));
        data.push_back(to_obj(args));
        break;
    }
    return static_cast<unsigned>(e.kind());
}

vm_obj expr_has_decidable_eq(vm_obj const & o1, vm_obj const & o2) {
    return mk_vm_bool(is_bi_equal(to_expr(o1), to_expr(o2)));
}

vm_obj expr_alpha_eqv(vm_obj const & o1, vm_obj const & o2) {
    return mk_vm_bool(to_expr(o1) == to_expr(o2));
}

vm_obj expr_to_string(vm_obj const &, vm_obj const & l) {
    std::ostringstream out;
    out << to_expr(l);
    return to_obj(out.str());
}

vm_obj expr_lt(vm_obj const & o1, vm_obj const & o2) {
    return mk_vm_bool(is_lt(to_expr(o1), to_expr(o2), true));
}

vm_obj expr_lex_lt(vm_obj const & o1, vm_obj const & o2) {
    return mk_vm_bool(is_lt(to_expr(o1), to_expr(o2), false));
}

vm_obj expr_fold(vm_obj const &, vm_obj const & e, vm_obj const & a, vm_obj const & fn) {
    vm_obj r = a;
    for_each(to_expr(e), [&](expr const & o, unsigned d) {
            r = invoke(fn, to_obj(o), mk_vm_nat(d), r);
            return true;
        });
    return r;
}

vm_obj expr_replace(vm_obj const & e, vm_obj const & fn) {
    expr r = replace(to_expr(e), [&](expr const & o, unsigned d) {
            vm_obj new_o = invoke(fn, to_obj(o), mk_vm_nat(d));
            if (is_none(new_o))
                return none_expr();
            else
                return some_expr(to_expr(get_some_value(new_o)));
        });
    return to_obj(r);
}

vm_obj expr_instantiate_univ_params(vm_obj const & e, vm_obj const & nls) {
  list<name> names = to_list<name>(nls, [](vm_obj const & p) {
    lean_assert(csize(p) == 2);
    return to_name(cfield(p, 0));
  } );
  list<level> levels = to_list<level>(nls, [](vm_obj const & p) {
    lean_assert(csize(p) == 2);
    return to_level(cfield(p, 1));
  } );
  return to_obj(instantiate_univ_params(to_expr(e), names, levels));
}

vm_obj expr_instantiate_var(vm_obj const & e, vm_obj const & v) {
    return to_obj(instantiate(to_expr(e), to_expr(v)));
}

vm_obj expr_instantiate_nth_var(vm_obj const & n, vm_obj const & e, vm_obj const & v) {
    auto u = to_unsigned(n);
    return to_obj(instantiate(to_expr(e), u, to_expr(v)));
}

vm_obj expr_instantiate_vars(vm_obj const & e, vm_obj const & vs) {
    buffer<expr> vs_buf;
    to_buffer_expr(vs, vs_buf);
    return to_obj(instantiate(to_expr(e), vs_buf.size(), vs_buf.data()));
}

vm_obj expr_abstract_local(vm_obj const & e, vm_obj const & n) {
    return to_obj(abstract_local(to_expr(e), to_name(n)));
}

static void list_name_to_buffer_local(vm_obj const & o, buffer<expr> & r) {
    if (is_simple(o)) {
        return;
    } else {
        expr dummy = mk_Prop();
        r.push_back(mk_local(to_name(cfield(o, 0)), dummy));
        list_name_to_buffer_local(cfield(o, 1), r);
    }
}

vm_obj expr_abstract_locals(vm_obj const & e, vm_obj const & ns) {
    buffer<expr> locals;
    list_name_to_buffer_local(ns, locals);
    return to_obj(abstract_locals(to_expr(e), locals.size(), locals.data()));
}

vm_obj expr_has_var(vm_obj const & e) {
    return mk_vm_bool(!closed(to_expr(e)));
}

vm_obj expr_get_free_var_range(vm_obj const & e) {
    return mk_vm_nat(get_free_var_range(to_expr(e)));
}

vm_obj expr_get_weight(vm_obj const & e) {
    return mk_vm_nat(get_weight(to_expr(e)));
}

vm_obj expr_get_depth(vm_obj const & e) {
    return mk_vm_nat(get_depth(to_expr(e)));
}

vm_obj expr_has_var_idx(vm_obj const & e, vm_obj const & u) {
    if (auto n = try_to_unsigned(u)) {
        return mk_vm_bool(has_free_var(to_expr(e), *n));
    } else {
        return mk_vm_false();
    }
}

vm_obj expr_has_local(vm_obj const & e) {
    return mk_vm_bool(has_local(to_expr(e)));
}

vm_obj expr_has_meta_var(vm_obj const & e) {
    return mk_vm_bool(has_metavar(to_expr(e)));
}

vm_obj expr_lift_vars(vm_obj const & e, vm_obj const & n1, vm_obj const & n2) {
    auto u1 = try_to_unsigned(n1);
    auto u2 = try_to_unsigned(n2);
    if (u1 && u2)
        return to_obj(lift_free_vars(to_expr(e), *u1, *u2));
    else
        return e;
}

vm_obj expr_lower_vars(vm_obj const & e, vm_obj const & n1, vm_obj const & n2) {
    auto u1 = try_to_unsigned(n1);
    auto u2 = try_to_unsigned(n2);
    if (u1 && u2)
        return to_obj(lower_free_vars(to_expr(e), *u1, *u2));
    else
        return e;
}

vm_obj expr_hash(vm_obj const & e) {
    unsigned r = to_expr(e).hash() % LEAN_MAX_SMALL_NAT;
    return mk_vm_simple(r); // make sure it is a simple value
}

vm_obj expr_copy_pos_info(vm_obj const & src, vm_obj const & tgt) {
    return to_obj(copy_tag(to_expr(src), copy(to_expr(tgt))));
}

vm_obj expr_is_internal_cnstr(vm_obj const & e) {
    auto opt_unsigned = is_internal_cnstr(to_expr(e));
    if (opt_unsigned) {
        std::cout << *opt_unsigned << std::endl;
        vm_obj u = to_obj(*opt_unsigned);
        return mk_vm_constructor(1, { u });
    } else {
        return mk_vm_constructor(0, {});
    }
}

vm_obj expr_is_internal_proj(vm_obj const & e) {
    auto opt_unsigned = is_internal_proj(to_expr(e));
    if (opt_unsigned) {
        std::cout << *opt_unsigned << std::endl;
        vm_obj u = to_obj(*opt_unsigned);
        return mk_vm_constructor(1, { u });
    } else {
        return mk_vm_constructor(0, {});
    }
}

vm_obj expr_is_internal_cases(vm_obj const & e) {
    auto opt_unsigned = is_internal_cases(to_expr(e));
    if (opt_unsigned) {
        std::cout << *opt_unsigned << std::endl;
        vm_obj u = to_obj(*opt_unsigned);
        return mk_vm_constructor(1, { u });
    } else {
        return mk_vm_constructor(0, {});
    }
}

vm_obj expr_get_nat_value(vm_obj const & o) {
    expr e = to_expr(o);
    if (is_nat_value(e)) {
        auto n = mk_vm_nat(get_nat_value_value(e));
        return mk_vm_constructor(1, { n });
    } else {
        return mk_vm_simple(0);
    }
}

vm_obj expr_collect_univ_params(vm_obj const & o) {
    list<name> param_list;
    collect_univ_params(to_expr(o), name_set()).for_each(
            [&] (name const & n) { param_list = cons(n, param_list); });
    return to_obj(param_list);
}

// TODO(Leo): move to a different file
vm_obj vm_mk_nat_val_ne_proof(vm_obj const & a, vm_obj const & b) {
    return to_obj(mk_nat_val_ne_proof(to_expr(a), to_expr(b)));
}

vm_obj vm_mk_nat_val_lt_proof(vm_obj const & a, vm_obj const & b) {
    return to_obj(mk_nat_val_lt_proof(to_expr(a), to_expr(b)));
}

vm_obj vm_mk_nat_val_le_proof(vm_obj const & a, vm_obj const & b) {
    return to_obj(mk_nat_val_le_proof(to_expr(a), to_expr(b)));
}

vm_obj vm_mk_fin_val_ne_proof(vm_obj const & a, vm_obj const & b) {
    return to_obj(mk_fin_val_ne_proof(to_expr(a), to_expr(b)));
}

vm_obj vm_mk_char_val_ne_proof(vm_obj const & a, vm_obj const & b) {
    return to_obj(mk_char_val_ne_proof(to_expr(a), to_expr(b)));
}

vm_obj vm_mk_string_val_ne_proof(vm_obj const & a, vm_obj const & b) {
    return to_obj(mk_string_val_ne_proof(to_expr(a), to_expr(b)));
}

vm_obj vm_mk_int_val_ne_proof(vm_obj const & a, vm_obj const & b) {
    return to_obj(mk_int_val_ne_proof(to_expr(a), to_expr(b)));
}

vm_obj expr_mk_sorry(vm_obj const & t) {
    return to_obj(mk_sorry(to_expr(t)));
}

vm_obj expr_is_sorry(vm_obj const & e_) {
    auto & e = to_expr(e_);
    return to_obj(is_sorry(e) ? some(sorry_type(e)) : none_expr());
}

vm_obj expr_occurs(vm_obj const & e1, vm_obj const & e2) {
    return mk_vm_bool(occurs(to_expr(e1), to_expr(e2)));
}

vm_obj expr_subst(vm_obj const &, vm_obj const & _e1, vm_obj const & _e2) {
    expr const & e1 = to_expr(_e1);
    expr const & e2 = to_expr(_e2);
    if (is_lambda(e1)) {
        return to_obj(instantiate(binding_body(e1), e2));
    } else {
        return to_obj(mk_app(e1, e2));
    }
}

vm_obj expr_is_annotation(vm_obj const &, vm_obj const & _e) {
    expr const & e = to_expr(_e);
    if (is_annotation(e)) {
        return mk_vm_some(mk_vm_pair(to_obj(get_annotation_kind(e)), to_obj(get_annotation_arg(e))));
    } else {
        return mk_vm_none();
    }
}

vm_obj reflect_expr(vm_obj const & elab, vm_obj const & e) {
    if (to_bool(elab))
        return to_obj(mk_elaborated_expr_quote(to_expr(e)));
    else
        return to_obj(mk_pexpr_quote_and_substs(to_expr(e), /* is_strict */ false));
}

vm_obj reflect_string(vm_obj const & s) {
    return to_obj(from_string(to_string(s)));
}

vm_obj expr_pos(vm_obj const &, vm_obj const & e) {
    if (auto p = get_pos_info(to_expr(e)))
        return mk_vm_some(to_obj(*p));
    return mk_vm_none();
}

vm_obj expr_has_local_in(vm_obj const & e, vm_obj const & s) {
    return mk_vm_bool(contains_local(to_expr(e), to_name_set(s)));
}

vm_obj expr_mk_delayed_abstraction(vm_obj const & e, vm_obj const & ns) {
    buffer<name> names;
    to_buffer_name(ns, names);
    return to_obj(mk_delayed_abstraction(to_expr(e), names));
}

void initialize_vm_expr() {
    DECLARE_VM_BUILTIN(name({"expr", "var"}),              expr_var_intro);
    DECLARE_VM_BUILTIN(name({"expr", "sort"}),             expr_sort_intro);
    DECLARE_VM_BUILTIN(name({"expr", "const"}),            expr_const_intro);
    DECLARE_VM_BUILTIN(name({"expr", "mvar"}),             expr_mvar_intro);
    DECLARE_VM_BUILTIN(name({"expr", "local_const"}),      expr_local_const_intro);
    DECLARE_VM_BUILTIN(name({"expr", "app"}),              expr_app_intro);
    DECLARE_VM_BUILTIN(name({"expr", "lam"}),              expr_lam_intro);
    DECLARE_VM_BUILTIN(name({"expr", "pi"}),               expr_pi_intro);
    DECLARE_VM_BUILTIN(name({"expr", "elet"}),             expr_elet_intro);
    DECLARE_VM_BUILTIN(name({"expr", "macro"}),            expr_macro_intro);
    DECLARE_VM_BUILTIN(name({"expr", "macro_def_name"}),   expr_macro_def_name);
    DECLARE_VM_BUILTIN(name({"expr", "has_decidable_eq"}), expr_has_decidable_eq);
    DECLARE_VM_BUILTIN(name({"expr", "alpha_eqv"}),        expr_alpha_eqv);
    DECLARE_VM_BUILTIN(name({"expr", "to_string"}),        expr_to_string);
    DECLARE_VM_BUILTIN(name({"expr", "lt"}),               expr_lt);
    DECLARE_VM_BUILTIN(name({"expr", "lex_lt"}),           expr_lex_lt);
    DECLARE_VM_BUILTIN(name({"expr", "fold"}),             expr_fold);
    DECLARE_VM_BUILTIN(name({"expr", "replace"}),          expr_replace);
    DECLARE_VM_BUILTIN(name({"expr", "instantiate_univ_params"}), expr_instantiate_univ_params);
    DECLARE_VM_BUILTIN(name({"expr", "instantiate_nth_var"}),     expr_instantiate_nth_var);
    DECLARE_VM_BUILTIN(name({"expr", "instantiate_var"}),  expr_instantiate_var);
    DECLARE_VM_BUILTIN(name({"expr", "instantiate_vars"}), expr_instantiate_vars);
    DECLARE_VM_BUILTIN(name({"expr", "subst"}),            expr_subst);
    DECLARE_VM_BUILTIN(name({"expr", "abstract_local"}),   expr_abstract_local);
    DECLARE_VM_BUILTIN(name({"expr", "abstract_locals"}),  expr_abstract_locals);
    DECLARE_VM_BUILTIN(name({"expr", "get_free_var_range"}),          expr_get_free_var_range);
    DECLARE_VM_BUILTIN(name({"expr", "get_weight"}),       expr_get_weight);
    DECLARE_VM_BUILTIN(name({"expr", "get_depth"}),        expr_get_depth);
    DECLARE_VM_BUILTIN(name({"expr", "has_var"}),          expr_has_var);
    DECLARE_VM_BUILTIN(name({"expr", "has_var_idx"}),      expr_has_var_idx);
    DECLARE_VM_BUILTIN(name({"expr", "has_local"}),        expr_has_local);
    DECLARE_VM_BUILTIN(name({"expr", "has_meta_var"}),     expr_has_meta_var);
    DECLARE_VM_BUILTIN(name({"expr", "lift_vars"}),        expr_lift_vars);
    DECLARE_VM_BUILTIN(name({"expr", "lower_vars"}),       expr_lower_vars);
    DECLARE_VM_BUILTIN(name({"expr", "hash"}),             expr_hash);
    DECLARE_VM_BUILTIN(name({"expr", "pos"}),              expr_pos);
    DECLARE_VM_BUILTIN(name({"expr", "copy_pos_info"}),    expr_copy_pos_info);
    DECLARE_VM_BUILTIN(name({"expr", "occurs"}),           expr_occurs);
    DECLARE_VM_BUILTIN(name({"expr", "collect_univ_params"}), expr_collect_univ_params);
    DECLARE_VM_BUILTIN(name({"expr", "has_local_in"}),     expr_has_local_in);

    DECLARE_VM_CASES_BUILTIN(name({"expr", "cases_on"}),   expr_cases_on);

    DECLARE_VM_BUILTIN(name("string", "reflect"),           reflect_string);
    DECLARE_VM_BUILTIN(name("expr", "reflect"),             reflect_expr);

    DECLARE_VM_BUILTIN(name("mk_nat_val_ne_proof"),        vm_mk_nat_val_ne_proof);
    DECLARE_VM_BUILTIN(name("mk_nat_val_lt_proof"),        vm_mk_nat_val_lt_proof);
    DECLARE_VM_BUILTIN(name("mk_nat_val_le_proof"),        vm_mk_nat_val_le_proof);
    DECLARE_VM_BUILTIN(name("mk_fin_val_ne_proof"),        vm_mk_fin_val_ne_proof);
    DECLARE_VM_BUILTIN(name("mk_char_val_ne_proof"),       vm_mk_char_val_ne_proof);
    DECLARE_VM_BUILTIN(name("mk_string_val_ne_proof"),     vm_mk_string_val_ne_proof);
    DECLARE_VM_BUILTIN(name("mk_int_val_ne_proof"),        vm_mk_int_val_ne_proof);

    DECLARE_VM_BUILTIN(name("expr", "is_annotation"),      expr_is_annotation);

    DECLARE_VM_BUILTIN(name("expr", "mk_sorry"), expr_mk_sorry);
    DECLARE_VM_BUILTIN(name("expr", "is_sorry"), expr_is_sorry);

    // Not sure if we should expose these or what?
    DECLARE_VM_BUILTIN(name({"expr", "is_internal_cnstr"}), expr_is_internal_cnstr);
    DECLARE_VM_BUILTIN(name({"expr", "get_nat_value"}), expr_get_nat_value);

    DECLARE_VM_BUILTIN(name({"expr", "mk_delayed_abstraction"}), expr_mk_delayed_abstraction);
}

void finalize_vm_expr() {
}

void initialize_vm_expr_builtin_idxs() {
}
}
