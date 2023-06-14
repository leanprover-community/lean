/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "util/fresh_name.h"
#include "kernel/environment.h"
#include "kernel/instantiate.h"
#include "kernel/abstract.h"
#include "kernel/inductive/inductive.h"
#include "kernel/type_checker.h"
#include "library/protected.h"
#include "library/module.h"
#include "library/util.h"
#include "library/reducible.h"
#include "library/constants.h"
#include "library/normalize.h"
#include "library/scoped_ext.h"
#include "library/aux_recursors.h"
#include "library/constructions/util.h"

namespace lean {
static void throw_corrupted(name const & n) {
    throw exception(sstream() << "error in 'no_confusion' generation, '" << n << "' inductive datatype declaration is corrupted");
}

optional<environment> mk_no_confusion_type(environment const & env, name const & n) {
    optional<inductive::inductive_decl> decl = inductive::is_inductive_decl(env, n);
    if (!decl)
        throw exception(sstream() << "error in 'no_confusion' generation, '" << n << "' is not an inductive datatype");
    if (is_inductive_predicate(env, n) || !can_elim_to_type(env, n))
        return optional<environment>();
    name_generator ngen    = mk_constructions_name_generator();
    unsigned nparams       = decl->m_num_params;
    declaration ind_decl   = env.get(n);
    declaration cases_decl = env.get(name(n, "cases_on"));
    level_param_names lps  = cases_decl.get_univ_params();
    level  plvl            = mk_param_univ(head(lps));
    levels ilvls           = param_names_to_levels(tail(lps));
    level rlvl             = plvl;
    expr ind_type          = instantiate_type_univ_params(ind_decl, ilvls);
    level ind_lvl          = get_datatype_level(env, ind_type);
    // All inductive datatype parameters and indices are arguments
    buffer<expr> args;
    ind_type = to_telescope(ind_type, args, some(mk_implicit_binder_info()));
    if (!is_sort(ind_type) || args.size() < nparams)
        throw_corrupted(n);
    unsigned nindices      = args.size() - nparams;
    // Create inductive datatype
    expr I = mk_app(mk_constant(n, ilvls), args);
    // Add (P : Type)
    expr P = mk_local(ngen.next(), "P", mk_sort(plvl), binder_info());
    args.push_back(P);
    // add v1 and v2 elements of the inductive type
    expr v1 = mk_local(ngen.next(), "v1", I, binder_info());
    expr v2 = mk_local(ngen.next(), "v2", I, binder_info());
    args.push_back(v1);
    args.push_back(v2);
    expr R = mk_sort(rlvl);
    expr Pres = P;
    name no_confusion_type_name{n, "no_confusion_type"};
    expr no_confusion_type_type = Pi(args, R);
    // Create type former
    buffer<expr> type_former_args;
    for (unsigned i = nparams; i < nparams + nindices; i++)
        type_former_args.push_back(args[i]);
    type_former_args.push_back(v1);
    expr type_former = Fun(type_former_args, R);
    // Create cases_on
    levels clvls   = levels(mk_succ(rlvl), ilvls);
    expr cases_on  = mk_app(mk_app(mk_constant(cases_decl.get_name(), clvls), nparams, args.data()), type_former);
    cases_on       = mk_app(cases_on, nindices, args.data() + nparams);
    expr cases_on1 = mk_app(cases_on, v1);
    expr cases_on2 = mk_app(cases_on, v2);
    type_checker tc(env);
    type_context_old ctx(env, transparency_mode::Semireducible);
    expr t1        = tc.infer(cases_on1);
    expr t2        = tc.infer(cases_on2);
    buffer<expr> outer_cases_on_args;
    unsigned idx1 = 0;
    while (is_pi(t1)) {
        buffer<expr> minor1_args;
        expr minor1 = to_telescope(tc, binding_domain(t1), minor1_args);
        expr curr_t2  = t2;
        buffer<expr> inner_cases_on_args;
        unsigned idx2 = 0;
        while (is_pi(curr_t2)) {
            buffer<expr> minor2_args;
            expr minor2 = to_telescope(tc, binding_domain(curr_t2), minor2_args);
            if (idx1 != idx2) {
                // infeasible case, constructors do not match
                inner_cases_on_args.push_back(Fun(minor2_args, Pres));
            } else {
                if (minor1_args.size() != minor2_args.size())
                    throw_corrupted(n);
                buffer<expr> rtype_hyp;
                // add equalities
                for (unsigned i = 0; i < minor1_args.size(); i++) {
                    expr lhs      = minor1_args[i];
                    expr rhs      = minor2_args[i];
                    expr lhs_type = mlocal_type(lhs);
                    if (!tc.is_prop(lhs_type)) {
                        expr rhs_type = mlocal_type(rhs);
                        level l       = sort_level(tc.ensure_type(lhs_type));
                        expr h_type;
                        // use `ctx` not `tc` here, as we want them to be reducibly defeq
                        if (ctx.is_def_eq(lhs_type, rhs_type)) {
                            h_type = mk_app(mk_constant(get_eq_name(), to_list(l)), lhs_type, lhs, rhs);
                        } else {
                            h_type = mk_app(mk_constant(get_heq_name(), to_list(l)), lhs_type, lhs, rhs_type, rhs);
                        }
                        rtype_hyp.push_back(mk_local(ngen.next(), mlocal_pp_name(lhs).append_after("_eq"), h_type, binder_info()));
                    }
                }
                inner_cases_on_args.push_back(Fun(minor2_args, mk_arrow(Pi(rtype_hyp, P), Pres)));
            }
            idx2++;
            curr_t2 = binding_body(curr_t2);
        }
        outer_cases_on_args.push_back(Fun(minor1_args, mk_app(cases_on2, inner_cases_on_args)));
        idx1++;
        t1 = binding_body(t1);
    }
    expr no_confusion_type_value = Fun(args, mk_app(cases_on1, outer_cases_on_args));

    declaration new_d = mk_definition_inferring_trusted(env, no_confusion_type_name, lps, no_confusion_type_type, no_confusion_type_value,
                                                        reducibility_hints::mk_abbreviation());
    environment new_env = module::add(env, check(env, new_d));
    new_env = set_reducible(new_env, no_confusion_type_name, reducible_status::Reducible, true);
    return some(add_protected(new_env, no_confusion_type_name));
}

environment mk_no_confusion(environment const & env, name const & n) {
    optional<environment> env1 = mk_no_confusion_type(env, n);
    if (!env1)
        return env;
    environment new_env = *env1;
    type_checker tc(new_env);
    name_generator ngen                = mk_constructions_name_generator();
    inductive::inductive_decl decl     = *inductive::is_inductive_decl(new_env, n);
    unsigned nparams                   = decl.m_num_params;
    declaration ind_decl               = env.get(n);
    declaration no_confusion_type_decl = new_env.get(name{n, "no_confusion_type"});
    declaration cases_decl             = new_env.get(name(n, "cases_on"));
    level_param_names lps              = no_confusion_type_decl.get_univ_params();
    levels ls                          = param_names_to_levels(lps);
    expr ind_type                      = instantiate_type_univ_params(ind_decl, tail(ls));
    level ind_lvl                      = get_datatype_level(env, ind_type);
    expr no_confusion_type_type        = instantiate_type_univ_params(no_confusion_type_decl, ls);
    buffer<expr> args;
    expr type = no_confusion_type_type;
    type = to_telescope(type, args, some(mk_implicit_binder_info()));
    lean_assert(args.size() >= nparams + 3);
    unsigned nindices = args.size() - nparams - 3; // 3 is for P v1 v2
    expr range        = mk_app(mk_constant(no_confusion_type_decl.get_name(), ls), args);
    expr P            = args[args.size()-3];
    expr v1           = args[args.size()-2];
    expr v2           = args[args.size()-1];
    expr v_type       = mlocal_type(v1);
    level v_lvl       = sort_level(tc.ensure_type(v_type));
    expr eq_v         = mk_app(mk_constant(get_eq_name(), to_list(v_lvl)), v_type);
    expr H12          = mk_local(ngen.next(), "h12", mk_app(eq_v, v1, v2), binder_info());
    args.push_back(H12);
    name no_confusion_name{n, "no_confusion"};
    expr no_confusion_ty = Pi(args, range);
    // The gen proof is of the form
    //   (fun H11 : v1 = v1, cases_on Params (fun Indices v1, no_confusion_type Params Indices P v1 v1) Indices v1
    //        <for-each case>
    //        (fun H : (equations -> P), H (refl) ... (refl))
    //        ...
    //   )

    // H11 is for creating the generalization
    expr H11          = mk_local(ngen.next(), "h11", mk_app(eq_v, v1, v1), binder_info());
    // Create the type former (fun Indices v1, no_confusion_type Params Indices P v1 v1)
    buffer<expr> type_former_args;
    for (unsigned i = nparams; i < nparams + nindices; i++)
        type_former_args.push_back(args[i]);
    type_former_args.push_back(v1);
    buffer<expr> no_confusion_type_args;
    for (unsigned i = 0; i < nparams + nindices; i++)
        no_confusion_type_args.push_back(args[i]);
    no_confusion_type_args.push_back(P);
    no_confusion_type_args.push_back(v1);
    no_confusion_type_args.push_back(v1);
    expr no_confusion_type_app = mk_app(mk_constant(no_confusion_type_decl.get_name(), ls), no_confusion_type_args);
    expr type_former = Fun(type_former_args, no_confusion_type_app);
    // create cases_on
    levels clvls   = ls;
    expr cases_on  = mk_app(mk_app(mk_constant(cases_decl.get_name(), clvls), nparams, args.data()), type_former);
    cases_on       = mk_app(mk_app(cases_on, nindices, args.data() + nparams), v1);
    expr cot       = tc.infer(cases_on);

    while (is_pi(cot)) {
        buffer<expr> minor_args;
        expr minor = to_telescope(tc, binding_domain(cot), minor_args);
        lean_assert(!minor_args.empty());
        expr H  = minor_args.back();
        expr Ht = mlocal_type(H);
        buffer<expr> refl_args;
        while (is_pi(Ht)) {
            buffer<expr> eq_args;
            expr eq_fn = get_app_args(binding_domain(Ht), eq_args);
            if (const_name(eq_fn) == get_eq_name()) {
                refl_args.push_back(mk_app(mk_constant(get_eq_refl_name(), const_levels(eq_fn)), eq_args[0], eq_args[2]));
            } else {
                refl_args.push_back(mk_app(mk_constant(get_heq_refl_name(), const_levels(eq_fn)), eq_args[0], eq_args[1]));
            }
            Ht = binding_body(Ht);
        }
        expr pr  = mk_app(H, refl_args);
        cases_on = mk_app(cases_on, Fun(minor_args, pr));
        cot = binding_body(cot);
    }
    expr gen = cases_on;
    gen = Fun(H11, gen);
    // Now, we use gen to build the final proof using eq.rec
    //
    //  eq.rec InductiveType v1 (fun (a : InductiveType), v1 = a -> no_confusion_type Params Indices v1 a) gen v2 H12 H12
    //
    level eq_rec_l1 = head(ls);
    expr eq_rec = mk_app(mk_constant(get_eq_rec_name(), {eq_rec_l1, v_lvl}), v_type, v1);
    // create eq_rec type_former
    //    (fun (a : InductiveType), v1 = a -> no_confusion_type Params Indices v1 a)
    expr a   = mk_local(ngen.next(), "a",   v_type, binder_info());
    expr H1a = mk_local(ngen.next(), "h1a", mk_app(eq_v, v1, a), binder_info());
    // reusing no_confusion_type_args... we just replace the last argument with a
    no_confusion_type_args.pop_back();
    no_confusion_type_args.push_back(a);
    expr no_confusion_type_app_1a = mk_app(mk_constant(no_confusion_type_decl.get_name(), ls), no_confusion_type_args);
    expr rec_type_former = Fun(a, Pi(H1a, no_confusion_type_app_1a));
    // finalize eq_rec
    eq_rec = mk_app(mk_app(eq_rec, rec_type_former, gen, v2, H12), H12);
    //
    expr no_confusion_val = Fun(args, eq_rec);
    declaration new_d = mk_definition_inferring_trusted(new_env, no_confusion_name, lps, no_confusion_ty, no_confusion_val,
                                                        reducibility_hints::mk_abbreviation());
    new_env = module::add(new_env, check(new_env, new_d));
    new_env = set_reducible(new_env, no_confusion_name, reducible_status::Reducible, true);
    new_env = add_no_confusion(new_env, no_confusion_name);
    return add_protected(new_env, no_confusion_name);
}
}
