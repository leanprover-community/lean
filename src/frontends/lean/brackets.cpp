/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/abstract.h"
#include "library/constants.h"
#include "library/placeholder.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/builtin_exprs.h"
#include "frontends/lean/util.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/structure_instance.h"

namespace lean {
/* Parse rest of the subtype expression prefix '{' id ':' expr '\\' ... */
static expr parse_subtype(parser & p, pos_info const & pos, expr const & local) {
    parser::local_scope scope(p);
    p.add_local(local);
    expr pred    = p.parse_expr();
    p.check_token_next(get_rcurly_tk(), "invalid subtype, '}' expected");
    bool use_cache = false;
    pred         = p.save_pos(Fun(local, pred, use_cache), pos);
    expr subtype = p.save_pos(mk_constant(get_subtype_name()), pos);
    return p.mk_app(subtype, pred, pos);
}

/* Parse rest of the set_of expression prefix '{' id ':' expr '|' ... */
static expr parse_set_of(parser & p, pos_info const & pos, expr const & local) {
    parser::local_scope scope(p);
    p.add_local(local);
    expr pred    = p.parse_expr();
    p.check_token_next(get_rcurly_tk(), "invalid set_of, '}' expected");
    bool use_cache = false;
    pred        = p.save_pos(Fun(local, pred, use_cache), pos);
    expr set_of = p.save_pos(mk_constant(get_set_of_name()), pos);
    return p.mk_app(set_of, pred, pos);
}

/* Parse rest of the set_replacement expression prefix '{' '(' expr ')' '|' ... */
static expr parse_set_replacement(parser & p, pos_info const & pos, expr const & hole_expr) {
    // At this point, we have parsed `hole_expr`, assuming all identifiers are local variables.
    // This will work, as long as we later update any identifiers that actually are globals.
    // So we parse the binders, assemble an expression for the characteristic predicate,
    // then use `patexpr_to_expr` to do the updating.
    buffer<expr> params;
    auto env = p.parse_binders(params, false);
    p.check_token_next(get_rcurly_tk(), "invalid set_replacement, '}' expected");

    // The predicate will look like `λ _x, ∃ p_1, ∃ p_2, ..., hole_expr[p_1, p_2, ...] = _x`.
    name x_name = name("_x");
    expr x = mk_local(x_name, p.save_pos(mk_expr_placeholder(), pos));
    // `hole_expr[p1, p2, ...] = _x`
    expr pred = p.mk_app(mk_constant(get_eq_name()), hole_expr, pos);
    pred = p.mk_app(pred, x, pos);

    expr exists = mk_constant(get_Exists_name());
    for (int i = params.size() - 1; i >= 0; i--) {
        // `∃ p_i, ∃ p_(i+1) ..., hole_expr[p_1, p_2, ...] = _x`
        pred = p.mk_app(exists, p.save_pos(Fun(params[i], pred), pos), pos);
    }
    // `λ _x, ∃ p_1, ∃ p_2, ..., hole_expr[p_1, p_2, ...] = _x`
    pred = p.save_pos(Fun(x, pred), pos);
    // Update identifiers so globals are actually globals.
    pred = p.patexpr_to_expr_core(pred);
    // `{_x | ∃ p_1, ∃ p_2, ..., hole_expr[p_1, p_2, ...] = _x}`
    return p.mk_app(mk_constant(get_set_of_name()), pred, pos);
}

/* Create singletoncollection for '{' expr '}' */
static expr mk_singleton(parser & p, pos_info const & pos, expr const & e) {
    return p.mk_app(p.save_pos(mk_constant(get_has_singleton_singleton_name()), pos), e, pos);
}

/* Parse rest of the insertable '{' expr ... */
static expr parse_fin_set(parser & p, pos_info const & pos, expr const & e) {
    lean_assert(p.curr_is_token(get_comma_tk()) || p.curr_is_token(get_rcurly_tk()));
    buffer<pair<pos_info, expr>> stack;
    stack.emplace_back(pos, e);
    while (p.curr_is_token(get_comma_tk())) {
        auto ins_pos = p.pos();
        p.next();
        if (p.curr_is_token(get_rcurly_tk())) break;
        expr e2 = p.parse_expr();
        stack.emplace_back(ins_pos, e2);
    }
    p.check_token_next(get_rcurly_tk(), "invalid explicit finite collection, '}' expected");
    unsigned i = stack.size() - 1;
    auto e2 = stack[i];
    expr r = mk_singleton(p, e2.first, e2.second);
    while (i--) {
        e2 = stack[i];
        expr insert = p.save_pos(mk_constant(get_has_insert_insert_name()), e2.first);
        r = p.rec_save_pos(mk_app(insert, e2.second, r), e2.first);
    }
    return r;
}

/* Parse rest of the sep expression '{' id '∈' ... */
static expr parse_sep(parser & p, pos_info const & pos, name const & id) {
    expr s = p.parse_expr();
    p.check_token_next(get_bar_tk(), "invalid sep expression, '|' expected");
    parser::local_scope scope(p);
    expr local = p.save_pos(mk_local(id, p.save_pos(mk_expr_placeholder(), pos)), pos);
    p.add_local(local);
    expr pred  = p.parse_expr();
    p.check_token_next(get_rcurly_tk(), "invalid sep expression, '}' expected");
    bool use_cache = false;
    pred   = p.rec_save_pos(Fun(local, pred, use_cache), pos);
    return p.rec_save_pos(mk_app(mk_constant(get_has_sep_sep_name()), pred, s), pos);
}

static expr parse_structure_instance_core(parser & p, optional<expr> const & src = {}, name const & S = {},
                                          buffer<name> fns = {}, buffer<expr> fvs = {}) {
    buffer<expr> sources;
    bool catchall = false;
    if (src)
        sources.push_back(*src);
    bool read_source = false;
    while (!p.curr_is_token(get_rcurly_tk())) {
        if (p.curr_is_token(get_dotdot_tk())) {
            p.next();
            if (p.curr_is_token(get_rcurly_tk())) {
                // ", ...}"
                catchall = true;
                break;
            }
            // ", ...src"
            sources.push_back(p.parse_expr());
            read_source = true;
        } else if (!read_source) {
            fns.push_back(p.check_id_next("invalid structure instance, identifier expected"));
            p.check_token_next(get_assign_tk(), "invalid structure instance, ':=' expected");
            fvs.push_back(p.parse_expr());
        } else {
            break;
        }
        // note: allows trailing ','
        if (p.curr_is_token(get_comma_tk())) {
            p.next();
        } else {
            break;
        }
    }
    p.check_token_next(get_rcurly_tk(), "invalid structure instance, '}' expected");
    return mk_structure_instance(S, fns, fvs, sources, catchall);
}

/* Parse rest of the qualified structure instance prefix '{' S '.' ... */
static expr parse_qualified_structure_instance(parser & p, name S, pos_info const & S_pos) {
    S = p.to_constant(S, "invalid structure name", S_pos);
    return parse_structure_instance_core(p, none_expr(), S);
}

/* Parse rest of the structure instance prefix '{' fname ... */
static expr parse_structure_instance(parser & p, name const & fname) {
    buffer<name> fns;
    buffer<expr> fvs;
    fns.push_back(fname);
    p.check_token_next(get_assign_tk(), "invalid structure instance, ':=' expected");
    fvs.push_back(p.parse_expr());
    if (p.curr_is_token(get_comma_tk()))
        p.next();
    return parse_structure_instance_core(p, none_expr(), name(), fns, fvs);
}

static name * g_emptyc_or_emptys = nullptr;

bool is_emptyc_or_emptys(expr const & e) {
    return is_constant(e, *g_emptyc_or_emptys);
}

expr parse_curly_bracket(parser & p, unsigned, expr const *, pos_info const & pos) {
    expr e;
    if (p.curr_is_token(get_rcurly_tk())) {
        p.next();
        return p.save_pos(mk_constant(*g_emptyc_or_emptys), pos);
    } else if (p.curr_is_identifier()) {
        auto id_pos = p.pos();
        name id     = p.get_name_val();
        p.next();
        if (p.curr_is_token(get_dslash_tk())) {
            expr type  = p.save_pos(mk_expr_placeholder(), id_pos);
            expr local = p.save_pos(mk_local(id, type), id_pos);
            p.next();
            return parse_subtype(p, pos, local);
        } else if (p.curr_is_token(get_bar_tk())) {
            expr type  = p.save_pos(mk_expr_placeholder(), id_pos);
            expr local = p.save_pos(mk_local(id, type), id_pos);
            p.next();
            return parse_set_of(p, pos, local);
        } else if (p.curr_is_token(get_colon_tk())) {
            p.next();
            expr type  = p.parse_expr();
            expr local = p.save_pos(mk_local(id, type), id_pos);
            if (p.curr_is_token(get_bar_tk())) {
                p.next();
                return parse_set_of(p, pos, local);
            } else {
                p.check_token_next(get_dslash_tk(), "invalid expression, '//' or '|' expected");
                return parse_subtype(p, pos, local);
            }
        } else if (p.curr_is_token(get_period_tk())) {
            p.next();
            return parse_qualified_structure_instance(p, id, id_pos);
        } else if (p.curr_is_token(get_assign_tk()) || p.curr_is_token(get_fieldarrow_tk())) {
            return parse_structure_instance(p, id);
        } else if (p.curr_is_token(get_membership_tk()) || p.curr_is_token(get_in_tk())) {
            p.next();
            return parse_sep(p, pos, id);
        } else {
            expr left = p.id_to_expr(id, id_pos);
            unsigned rbp = 0;
            while (rbp < p.curr_lbp()) {
                left = p.parse_led(left);
            }
            e = left;
        }
    } else if (p.curr_is_token(get_lparen_tk())) {
        // '{' '(' expr ')' '|' binders '}'
        // The expression is parsed before the binders, so we need to make a new scope here.
        // We assume for now all identifiers are in this scope,
        // and parse_set_replacement will update any variables once it determines the actual binders.
        e = (parser::local_scope(p), parser::all_id_local_scope(p),
            p.parse_expr()); // parses the `'(' expr ')'` part of the expression
        if (p.curr_is_token(get_bar_tk())) {
            p.next();
            return parse_set_replacement(p, pos, e);
        } else if (p.curr_is_token(get_comma_tk()) || p.curr_is_token(get_rcurly_tk())) {
            return parse_fin_set(p, pos, p.patexpr_to_expr_core(e));
        } else {
            p.maybe_throw_error({"invalid set replacement notation, ',', '}', or `|` expected", p.pos()});
            return mk_singleton(p, pos, p.patexpr_to_expr_core(e));
        }
    } else if (p.curr_is_token(get_period_tk())) {
        p.next();
        p.check_token_next(get_rcurly_tk(), "invalid empty structure instance, '}' expected");
        return p.save_pos(mk_structure_instance(), pos);
    } else if (p.curr_is_token(get_dotdot_tk())) {
        return parse_structure_instance_core(p);
    } else {
        e = p.parse_expr();
    }

    if (p.curr_is_token(get_comma_tk())) {
        return parse_fin_set(p, pos, e);
    } else if (p.curr_is_token(get_rcurly_tk())) {
        return parse_fin_set(p, pos, e);
    } else if (p.curr_is_token(get_with_tk())) {
        p.next();
        return parse_structure_instance_core(p, some_expr(e));
    } else {
        return p.parser_error_or_expr({"invalid '{' expression, ',', '}', '..', `//` or `|` expected", p.pos()});
    }
}

void initialize_brackets() {
    g_emptyc_or_emptys = new name("_emptyc_or_emptys");
}

void finalize_brackets() {
    delete g_emptyc_or_emptys;
}
}
