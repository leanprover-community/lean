/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sexpr/option_declarations.h"
#include "util/sstream.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "library/annotation.h"
#include "library/placeholder.h"
#include "library/explicit.h"
#include "library/aliases.h"
#include "library/scoped_ext.h"
#include "library/typed_expr.h"
#include "library/choice.h"
#include "library/constants.h"
#include "library/quote.h"
#include "library/string.h"
#include "library/trace.h"
#include "library/kernel_serializer.h"
#include "library/tactic/elaborate.h"
#include "library/tactic/smt/hinst_lemmas.h"
#include "library/equations_compiler/equations.h"
#include "frontends/lean/builtin_exprs.h"
#include "frontends/lean/decl_cmds.h"
#include "frontends/lean/token_table.h"
#include "frontends/lean/calc.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/match_expr.h"
#include "frontends/lean/decl_util.h"
#include "frontends/lean/brackets.h"
#include "frontends/lean/tactic_notation.h"
#include "frontends/lean/elaborator.h"

#ifndef LEAN_DEFAULT_PARSER_CHECKPOINT_HAVE
#define LEAN_DEFAULT_PARSER_CHECKPOINT_HAVE true
#endif

namespace lean {
static name * g_parser_checkpoint_have = nullptr;

bool get_parser_checkpoint_have(options const & opts) {
    return opts.get_bool(*g_parser_checkpoint_have, LEAN_DEFAULT_PARSER_CHECKPOINT_HAVE);
}

using namespace notation; // NOLINT

expr mk_annotation_with_pos(parser & p, name const & a, expr const & e, pos_info const & pos) {
    expr r = mk_annotation(a, e);
    r.set_tag(nulltag); // mk_annotation copies e's tag
    return p.save_pos(r, pos);
}

static name * g_no_universe_annotation = nullptr;

bool is_sort_wo_universe(expr const & e) {
    return is_annotation(e, *g_no_universe_annotation);
}

expr mk_sort_wo_universe(parser & p, ast_data & data, bool is_type) {
    level l = is_type ? mk_level_one() : mk_level_zero();
    expr r = p.save_pos((scoped_expr_caching(false), mk_sort(l)), data.m_start);
    p.set_ast_pexpr(data.m_id, r);
    r = mk_annotation_with_pos(p, *g_no_universe_annotation, r, data.m_start);
    p.set_ast_pexpr(data.m_id, r);
    return r;
}

static expr parse_Type(parser & p, unsigned, expr const *, pos_info const & pos) {
    auto& data = p.new_ast("Type", pos);
    if (p.curr_is_token(get_llevel_curly_tk())) {
        p.next();
        ast_id id; level l;
        std::tie(id, l) = p.parse_level();
        p.check_token_next(get_rcurly_tk(), "invalid Type expression, '}' expected");
        l = mk_succ(l);
        expr r = p.save_pos((scoped_expr_caching(false), mk_sort(l)), pos);
        p.set_ast_pexpr(data.push(id).m_id, r);
        return r;
    } else {
        return mk_sort_wo_universe(p, data.push(0), true);
    }
}

static expr parse_Sort(parser & p, unsigned, expr const *, pos_info const & pos) {
    auto& data = p.new_ast("Sort", pos);
    if (p.curr_is_token(get_llevel_curly_tk())) {
        p.next();
        ast_id id; level l;
        std::tie(id, l) = p.parse_level();
        p.check_token_next(get_rcurly_tk(), "invalid Sort expression, '}' expected");
        expr r = p.save_pos((scoped_expr_caching(false), mk_sort(l)), pos);
        p.set_ast_pexpr(data.push(id).m_id, r);
        return r;
    } else {
        return mk_sort_wo_universe(p, data.push(0), false);
    }
}

static expr parse_Type_star(parser & p, unsigned, expr const *, pos_info const & pos) {
    level l = mk_succ(mk_level_placeholder());
    expr r = p.save_pos((scoped_expr_caching(false), mk_sort(l)), pos);
    p.set_ast_pexpr(p.new_ast("Type*", pos).m_id, r);
    return r;
}

static expr parse_Sort_star(parser & p, unsigned, expr const *, pos_info const & pos) {
    level l = mk_level_placeholder();
    expr r = p.save_pos((scoped_expr_caching(false), mk_sort(l)), pos);
    p.set_ast_pexpr(p.new_ast("Sort*", pos).m_id, r);
    return r;
}

static name * g_let_match_name = nullptr;

static pair<ast_id, expr> parse_let(parser & p, pos_info const & pos, ast_data & group, bool in_do_block);
static expr parse_do(parser & p, ast_data & group, bool has_braces);
static pair<ast_id, expr> parse_let_body(parser & p, pos_info const & pos, ast_id last, ast_data & group, bool in_do_block) {
    if (in_do_block) {
        if (p.curr_is_token(get_in_tk())) {
            p.next();
            ast_id args = p.new_ast("args", pos).push(last).m_id;
            expr e = p.parse_expr();
            ast_id let = p.new_ast(get_let_tk(), pos).push(args).push(p.get_id(e)).m_id;
            group.push(p.new_ast("eval", pos).push(let).m_id);
            return {0, e};
        } else {
            p.check_token_next(get_comma_tk(), "invalid 'do' block 'let' declaration, ',' or 'in' expected");
            group.push(p.new_ast(get_let_tk(), pos).push(last).m_id);
            if (p.curr_is_token(get_let_tk())) {
                p.next();
                return parse_let(p, pos, group, in_do_block);
            } else {
                return {0, parse_do(p, group, false)};
            }
        }
    } else {
        group.push(last);
        if (p.curr_is_token(get_comma_tk())) {
            p.next();
            return parse_let(p, pos, group, in_do_block);
        } else if (p.curr_is_token(get_in_tk())) {
            p.next();
        } else {
            p.maybe_throw_error({"invalid let declaration, 'in' or ',' expected", p.pos()});
        }
        expr e = p.parse_expr();
        return {p.new_ast(get_let_tk(), pos).push(group.m_id).push(p.get_id(e)).m_id, e};
    }
}

// Distribute mk_typed_expr over choice expression.
// see issue #768
static expr mk_typed_expr_distrib_choice(parser & p, expr const & type, expr const & value, pos_info const & pos) {
    if (is_choice(value)) {
        buffer<expr> new_choices;
        for (unsigned i = 0; i < get_num_choices(value); i++) {
            new_choices.push_back(mk_typed_expr_distrib_choice(p, type, get_choice(value, i), pos));
        }
        return p.save_pos(mk_choice(new_choices.size(), new_choices.data()), pos);
    } else {
        return p.save_pos(mk_typed_expr(type, value), pos);
    }
}

static pair<ast_id, expr> parse_let(parser & p, pos_info const & pos, ast_data & group, bool in_do_block) {
    parser::local_scope scope1(p);
    ast_id nota;
    if (!in_do_block && (nota = p.parse_local_notation_decl())) {
        return parse_let_body(p, pos, nota, group, in_do_block);
    } else if (p.curr_is_identifier()) {
        auto id_pos     = p.pos();
        ast_id id_ast; name id;
        std::tie(id_ast, id) = p.check_atomic_id_next("invalid let declaration, atomic identifier expected");
        auto& var = p.new_ast("var", id_pos).push(id_ast);
        expr type;
        expr value;
        if (p.curr_is_token(get_assign_tk())) {
            p.next();
            type  = p.save_pos(mk_expr_placeholder(), id_pos);
            value = p.parse_expr();
            var.push(0).push(0).push(p.get_id(value));
        } else if (p.curr_is_token(get_colon_tk())) {
            p.next();
            type = p.parse_expr();
            p.check_token_next(get_assign_tk(), "invalid declaration, ':=' expected");
            value = p.parse_expr();
            var.push(0).push(p.get_id(type)).push(p.get_id(value));
        } else {
            parser::local_scope scope2(p);
            buffer<expr> ps;
            unsigned rbp = 0;
            auto& bis = p.new_ast("binders", p.pos());
            auto lenv = p.parse_binders(&bis, ps, rbp);
            var.push(bis.m_id);
            if (p.curr_is_token(get_colon_tk())) {
                p.next();
                type  = p.parse_scoped_expr(ps, lenv);
                var.push(p.get_id(type));
                type  = Pi(ps, type, p);
            } else {
                type  = p.save_pos(mk_expr_placeholder(), id_pos);
                var.push(0);
            }
            p.check_token_next(get_assign_tk(), "invalid let declaration, ':=' expected");
            value = p.parse_scoped_expr(ps, lenv);
            var.push(p.get_id(value));
            value = Fun(ps, value, p);
        }
        expr x = p.save_pos(mk_local(id, type), id_pos);
        p.add_local_expr(id, x);
        auto r = parse_let_body(p, pos, var.m_id, group, in_do_block);
        r.second = p.save_pos(mk_let(id, type, value, abstract_local(r.second, x)), pos);
        return r;
    } else {
        buffer<expr> new_locals;
        auto& var = p.new_ast("pat", p.pos());
        expr lhs = p.parse_pattern(new_locals);
        p.check_token_next(get_assign_tk(), "invalid let declaration, ':=' expected");
        expr value = p.parse_expr();
        var.push(p.get_id(lhs)).push(p.get_id(value));
        for (expr const & l : new_locals)
            p.add_local(l);
        ast_id ast; expr body;
        std::tie(ast, body) = parse_let_body(p, pos, var.m_id, group, in_do_block);
        match_definition_scope match_scope(p.env());
        expr fn = p.save_pos(mk_local(p.next_name(), *g_let_match_name, mk_expr_placeholder(), mk_rec_info(true)), pos);
        expr eqn = Fun(fn, Fun(new_locals, p.save_pos(mk_equation(p.rec_save_pos(mk_app(fn, lhs), pos), body), pos), p), p);
        equations_header h = mk_match_header(match_scope.get_name(), match_scope.get_actual_name());
        expr eqns  = p.save_pos(mk_equations(h, 1, &eqn), pos);
        return {ast, p.save_pos(mk_app(eqns, value), pos)};
    }
}

static expr parse_let_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    bool in_do_block = false;
    auto& group = p.new_ast("args", p.pos());
    ast_id id; expr r;
    std::tie(id, r) = parse_let(p, pos, group, in_do_block);
    p.set_ast_pexpr(id, r);
    return r;
}

static name * g_do_match_name = nullptr;

static std::tuple<optional<expr>, expr, expr, optional<expr>>
parse_do_action(parser & p, ast_data & parent, buffer<expr> & new_locals) {
    auto lhs_pos = p.pos();
    optional<expr> lhs = some(p.parse_pattern_or_expr());
    ast_id lhs_id = p.get_id(*lhs);
    expr type, curr;
    optional<expr> else_case;
    if (p.curr_is_token(get_colon_tk())) {
        p.next();
        type = p.parse_expr();
        if (is_placeholder(*lhs)) {
            lhs = mk_local("_x", type);
        }
        if (!is_local(*lhs)) {
            p.maybe_throw_error({"invalid 'do' block, unexpected ':' the left hand side is a pattern", lhs_pos});
            lhs = mk_local("_x", type);
        }
        lhs = p.save_pos(mk_local(mlocal_pp_name(*lhs), type), lhs_pos);
        new_locals.clear();
        new_locals.push_back(*lhs);
        p.check_token_next(get_larrow_tk(), "invalid 'do' block, '←' expected");
        curr = p.parse_expr();
        parent.push(p.new_ast(get_larrow_tk(), lhs_pos)
            .push(lhs_id).push(p.get_id(type)).push(p.get_id(curr)).push(0).m_id);
    } else if (p.curr_is_token(get_larrow_tk())) {
        p.next();
        type = p.save_pos(mk_expr_placeholder(), lhs_pos);
        bool skip_main_fn = false;
        lhs = p.patexpr_to_pattern(*lhs, skip_main_fn, new_locals);
        curr = p.parse_expr();
        ast_id else_id = 0;
        if (p.curr_is_token(get_bar_tk())) {
            p.next();
            else_case = p.parse_expr();
            else_id = p.get_id(*else_case);
        }
        parent.push(p.new_ast(get_larrow_tk(), lhs_pos)
            .push(lhs_id).push(0).push(p.get_id(curr)).push(else_id).m_id);
    } else {
        curr = p.patexpr_to_expr(*lhs);
        type = p.save_pos(mk_expr_placeholder(), lhs_pos);
        lhs  = none_expr();
        parent.push(p.new_ast("eval", lhs_pos).push(lhs_id).m_id);
    }
    return std::make_tuple(lhs, type, curr, else_case);
}

static expr mk_bind_fn(parser & p) {
    return mk_no_info(p.id_to_expr("bind", p.new_ast("bind", {}), /* resolve_only */ true));
}

static name * g_do_failure_eq = nullptr;

/* Mark for automatic failure equation when pattern matching in do-expressions. */
expr mark_do_failure_eq(expr const & e) {
    return mk_annotation(*g_do_failure_eq, e);
}

bool is_do_failure_eq(expr const & e) {
    auto it = e;
    while (is_lambda(it))
        it = binding_body(it);
    if (!is_equation(it)) return false;
    return is_annotation(equation_rhs(it), *g_do_failure_eq);
}

static expr parse_do(parser & p, ast_data & group, bool has_braces) {
    parser::local_scope scope(p);
    buffer<expr>               es;
    buffer<pos_info>           ps;
    buffer<optional<expr>>     lhss;
    buffer<optional<expr>>     else_cases;
    buffer<list<expr>>         lhss_locals;
    while (true) {
        if (p.curr_is_token(get_let_tk())) {
            auto pos = p.pos();
            p.next();
            bool in_do_block = true;
            es.push_back(parse_let(p, pos, group, in_do_block).second);
            break;
        } else {
            auto lhs_pos = p.pos();
            ps.push_back(lhs_pos);
            buffer<expr> new_locals;
            optional<expr> lhs, else_case;
            expr type, curr;
            std::tie(lhs, type, curr, else_case) = parse_do_action(p, group, new_locals);
            es.push_back(curr);
            if (p.curr_is_token(get_comma_tk())) {
                p.next();
                for (expr const & l : new_locals)
                    p.add_local(l);
                if (lhs && !is_local(*lhs)) {
                    // if lhs is a pattern, we need to save the locals to create the match
                    lhss_locals.push_back(to_list(new_locals));
                } else {
                    lhss_locals.push_back(list<expr>());
                }
                lhss.push_back(lhs);
                else_cases.push_back(else_case);
            } else {
                if (lhs) {
                    p.maybe_throw_error({"the last statement in a 'do' block must be an expression", lhs_pos});
                }
                break;
            }
        }
    }
    if (has_braces) {
        p.check_token_next(get_rcurly_tk(), "invalid 'do' block, '}' expected");
    }
    lean_assert(!es.empty());
    lean_assert(es.size() == lhss.size() + 1);
    if (es.size() == 1)
        return es[0];
    unsigned i = es.size();
    --i;
    expr r = es[i];
    while (i > 0) {
        --i;
        if (auto lhs = lhss[i]) {
            if (is_local(*lhs)) {
                r = p.rec_save_pos(mk_app(p.save_pos(mk_bind_fn(p), ps[i]), es[i], Fun(*lhs, r, p)), ps[i]);
            } else {
                // must introduce a "fake" match
                auto pos   = ps[i];
                match_definition_scope match_scope(p.env());
                expr fn = p.save_pos(mk_local(p.next_name(), *g_do_match_name, mk_expr_placeholder(), mk_rec_info(true)), pos);
                buffer<expr> locals;
                to_buffer(lhss_locals[i], locals);
                buffer<expr> eqs;
                eqs.push_back(Fun(fn, Fun(locals, p.save_pos(mk_equation(p.rec_save_pos(mk_app(fn, *lhs), pos), r), pos), p), p));
                expr else_case;
                bool ignore_if_unused;
                if (optional<expr> r = else_cases[i]) {
                    else_case        = *r;
                    ignore_if_unused = false;
                } else {
                    else_case        = p.save_pos(mark_do_failure_eq(p.save_pos(mk_constant(get_match_failed_name()), pos)), pos);
                    ignore_if_unused = true;
                }
                // add case
                //    _ := else_case
                expr x = mk_local(p.next_name(), "_x", mk_expr_placeholder(), binder_info());
                expr else_eq = Fun(fn, Fun(x, p.save_pos(mk_equation(p.rec_save_pos(mk_app(fn, x), pos),
                                                                     else_case,
                                                                     ignore_if_unused),
                                                         pos), p), p);
                eqs.push_back(else_eq);
                equations_header h = mk_match_header(match_scope.get_name(), match_scope.get_actual_name());
                expr eqns  = p.save_pos(mk_equations(h, eqs.size(), eqs.data()), pos);
                expr local = mk_local("_p", mk_expr_placeholder());
                expr match = p.mk_app(eqns, local, pos);
                r = p.rec_save_pos(mk_app(p.save_pos(mk_bind_fn(p), ps[i]),
                                          es[i],
                                          p.save_pos(Fun(local, match, p), pos)),
                                   pos);
            }
        } else {
            r = p.rec_save_pos(mk_app(p.save_pos(mk_bind_fn(p), ps[i]),
                                      es[i],
                                      p.save_pos(mk_lambda("_x", mk_expr_placeholder(), r), p.pos_of(r))),
                               ps[i]);
        }
    }
    return r;
}

static expr parse_do_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    bool has_braces = false;
    auto& data = p.new_ast("do", pos);
    if (p.curr_is_token(get_lcurly_tk())) {
        has_braces = true;
        data.m_value = "{";
        p.next();
    }
    expr r = parse_do(p, data, has_braces);
    p.set_ast_pexpr(data.m_id, r);
    return r;
}

static expr parse_unit(parser & p, unsigned, expr const *, pos_info const & pos) {
    auto e = p.save_pos(mk_constant(get_unit_star_name()), pos);
    p.set_ast_pexpr(p.new_ast("()", pos).m_id, e);
    return e;
}

static pair<ast_id, expr> parse_proof(parser & p) {
    expr e;
    if (p.curr_is_token(get_from_tk())) {
        auto& data = p.new_ast(get_from_tk(), p.pos());
        // parse: 'from' expr
        p.next();
        e = p.parse_expr();
        data.push(p.get_id(e));
        return {data.m_id, e};
    } else if (p.curr_is_token(get_begin_tk())) {
        auto pos = p.pos();
        e = parse_begin_end_expr(p, pos);
    } else if (p.curr_is_token(get_lcurly_tk())) {
        auto pos = p.pos();
        e = parse_curly_begin_end_expr(p, pos);
    } else if (p.curr_is_token(get_by_tk())) {
        auto pos = p.pos();
        e = parse_by(p, 0, nullptr, pos);
    } else {
        e = p.parser_error_or_expr({"invalid expression, 'by', 'begin', '{', or 'from' expected", p.pos()});
    }
    return {p.get_id(e), e};
}

static expr parse_have(parser & p, unsigned, expr const *, pos_info const & pos) {
    name id;
    expr prop;
    auto& data = p.new_ast("have", pos);
    if (p.curr_is_identifier()) {
        id = p.get_name_val();
        auto& id_ast = p.new_ast("ident", p.pos(), id);
        p.next();
        if (p.curr_is_token(get_colon_tk())) {
            p.next();
            prop      = p.parse_expr();
            data.push(id_ast.m_id).push(p.get_id(prop));
        } else {
            expr left = p.id_to_expr(id, id_ast);
            id        = get_this_tk();
            unsigned rbp = 0;
            while (rbp < p.curr_lbp()) {
                left = p.parse_led(left);
            }
            prop      = left;
            data.push(0).push(p.get_id(prop));
        }
    } else {
        id            = get_this_tk();
        prop          = p.parse_expr();
        data.push(0).push(p.get_id(prop));
    }
    expr proof;
    if (p.curr_is_token(get_assign_tk())) {
        auto& ast = p.new_ast(get_assign_tk(), p.pos());
        p.next();
        proof = p.parse_expr();
        data.push(ast.push(p.get_id(proof)).m_id);
    } else {
        p.check_token_next(get_comma_tk(), "invalid 'have' declaration, ',' expected");
        ast_id id;
        std::tie(id, proof) = parse_proof(p);
        data.push(id);
    }
    p.check_token_next(get_comma_tk(), "invalid 'have' declaration, ',' expected");
    parser::local_scope scope(p);
    expr l = p.save_pos(mk_local(id, prop), pos);
    p.add_local(l);
    expr body = p.parse_expr();
    data.push(p.get_id(body));
    body = abstract(body, l);
    if (get_parser_checkpoint_have(p.get_options()))
        body = mk_checkpoint_annotation(body);
    expr r = p.save_pos(mk_have_annotation(p.save_pos(mk_lambda(id, prop, body), pos)), pos);
    r = p.mk_app(r, proof, pos);
    p.set_ast_pexpr(data.m_id, r);
    return r;
}

static expr parse_show(parser & p, unsigned, expr const *, pos_info const & pos) {
    expr prop  = p.parse_expr();
    p.check_token_next(get_comma_tk(), "invalid 'show' declaration, ',' expected");
    ast_id id; expr proof;
    std::tie(id, proof) = parse_proof(p);
    expr b = p.save_pos(mk_lambda(get_this_tk(), prop, Var(0)), pos);
    expr r = p.mk_app(b, proof, pos);
    r = p.save_pos(mk_show_annotation(r), pos);
    p.set_ast_pexpr(p.new_ast("show", pos).push(p.get_id(prop)).push(id).m_id, r);
    return r;
}

static expr parse_suffices(parser & p, unsigned, expr const *, pos_info const & pos) {
    auto prop_pos = p.pos();
    name id;
    expr from;
    auto& data = p.new_ast("suffices", pos);
    if (p.curr_is_identifier()) {
        id = p.get_name_val();
        auto& id_ast = p.new_ast("ident", prop_pos, id);
        p.next();
        if (p.curr_is_token(get_colon_tk())) {
            p.next();
            from = p.parse_expr();
            data.push(id_ast.m_id).push(p.get_id(from));
        } else {
            expr left = p.id_to_expr(id, id_ast);
            id        = get_this_tk();
            unsigned rbp = 0;
            while (rbp < p.curr_lbp()) {
                left = p.parse_led(left);
            }
            from = left;
            data.push(0).push(p.get_id(from));
        }
    } else {
        id    = get_this_tk();
        from  = p.parse_expr();
        data.push(0).push(p.get_id(from));
    }
    expr local = p.save_pos(mk_local(id, from), prop_pos);
    p.check_token_next(get_comma_tk(), "invalid 'suffices' declaration, ',' expected");
    expr body;
    {
        parser::local_scope scope(p);
        p.add_local(local);
        ast_id id;
        std::tie(id, body) = parse_proof(p);
        data.push(id);
    }
    expr proof = p.save_pos(Fun(local, body, p), pos);
    p.check_token_next(get_comma_tk(), "invalid 'suffices' declaration, ',' expected");
    expr rest  = p.parse_expr();
    data.push(p.get_id(rest));
    expr r = p.mk_app(proof, rest, pos);
    r = p.save_pos(mk_suffices_annotation(r), pos);
    p.set_ast_pexpr(data.m_id, r);
    return r;
}

static expr * g_not  = nullptr;
static unsigned g_then_else_prec = 0;

static expr parse_ite(parser & p, ast_data & parent, expr const & c, pos_info const & pos) {
    if (!p.env().find(get_ite_name()))
        throw parser_error("invalid use of 'if-then-else' expression, environment does not contain 'ite' definition", pos);
    p.check_token_next(get_then_tk(), "invalid 'if-then-else' expression, 'then' expected");
    expr t = p.parse_expr(g_then_else_prec);
    p.check_token_next(get_else_tk(), "invalid 'if-then-else' expression, 'else' expected");
    expr e = p.parse_expr(g_then_else_prec);
    parent.push(p.get_id(t)).push(p.get_id(e));
    return p.save_pos(mk_app(mk_constant(get_ite_name()), c, t, e), pos);
}

static expr parse_dite(parser & p, ast_data & parent, name const & H_name, expr const & c, pos_info const & pos) {
    p.check_token_next(get_then_tk(), "invalid 'if-then-else' expression, 'then' expected");
    expr t, e;
    {
        parser::local_scope scope(p);
        expr H = mk_local(H_name, c);
        p.add_local(H);
        auto pos = p.pos();
        t = p.parse_expr(g_then_else_prec);
        parent.push(p.get_id(t));
        t = p.save_pos(Fun(H, t, p), pos);
    }
    p.check_token_next(get_else_tk(), "invalid 'if-then-else' expression, 'else' expected");
    {
        parser::local_scope scope(p);
        expr H = mk_local(H_name, mk_app(*g_not, c));
        p.add_local(H);
        auto pos = p.pos();
        e = p.parse_expr(g_then_else_prec);
        parent.push(p.get_id(e));
        e = p.save_pos(Fun(H, e, p), pos);
    }
    return p.save_pos(mk_app(p.save_pos(mk_constant(get_dite_name()), pos), c, t, e), pos);
}

static expr parse_if_then_else(parser & p, unsigned, expr const *, pos_info const & pos) {
    ast_id id; optional<name> hyp; expr cond;
    std::tie(id, hyp, cond) = p.parse_qualified_expr();
    auto& data = p.new_ast("if", pos).push(id).push(p.get_id(cond));
    auto r = hyp ? parse_dite(p, data, *hyp, cond, pos) : parse_ite(p, data, cond, pos);
    p.set_ast_pexpr(data.m_id, r);
    return r;
}

static expr parse_calc_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    return parse_calc(p, pos);
}

static expr parse_explicit_core(parser & p, pos_info const & pos, bool partial) {
    auto sym = partial ? "@@" : "@";
    if (!p.curr_is_identifier())
        return p.parser_error_or_expr({sstream() << "invalid '" << sym << "', identifier expected", p.pos()});
    expr fn = p.parse_id(/* allow_field_notation */ false);
    if (is_choice(fn)) {
        sstream s;
        s << "invalid '" << sym << "', function is overloaded, use fully qualified names (overloads: ";
        for (unsigned i = 0; i < get_num_choices(fn); i++) {
            if (i > 0) s << ", ";
            expr const & c = get_choice(fn, i);
            if (is_constant(c))
                s << const_name(c);
            else if (is_local(c))
                s << mlocal_pp_name(c);
            else
                s << "[other]";
        }
        s << ")";
        return p.parser_error_or_expr({s, pos});
    } else if (!is_as_atomic(fn) && !is_constant(fn) && !is_local(fn)) {
        return p.parser_error_or_expr({sstream() << "invalid '" << sym << "', function must be a constant or variable", pos});
    }
    expr r;
    if (partial)
        r = p.save_pos(mk_partial_explicit(fn), pos);
    else
        r = p.save_pos(mk_explicit(fn), pos);
    p.set_ast_pexpr(p.new_ast(sym, pos).push(p.get_id(fn)).m_id, r);
    return r;
}

static expr parse_explicit_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    return parse_explicit_core(p, pos, false);
}

static expr parse_partial_explicit_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    return parse_explicit_core(p, pos, true);
}

static expr parse_sorry(parser & p, unsigned, expr const *, pos_info const & pos) {
    auto r = p.mk_sorry(pos);
    p.set_ast_pexpr(p.new_ast("sorry", pos).m_id, r);
    return r;
}

static expr parse_pattern(parser & p, unsigned, expr const * args, pos_info const & pos) {
    auto r = p.save_pos(mk_pattern_hint(args[0]), pos);
    p.set_ast_pexpr(p.new_ast("(:", pos).push(p.get_id(args[0])).m_id, r);
    return r;
}

static expr parse_lazy_quoted_pexpr(parser & p, unsigned, expr const *, pos_info const & pos) {
    if (p.in_quote())
        return p.parser_error_or_expr({"invalid nested quoted expression", pos});
    parser::quote_scope scope1(p, true);
    restore_decl_meta_scope scope2;
    expr e = p.parse_expr();
    auto& data = p.new_ast("```()", pos);
    if (p.curr_is_token(get_colon_tk())) {
        p.next();
        expr t = p.parse_expr();
        ast_id id = p.new_ast(get_colon_tk(), p.pos_of(e)).push(p.get_id(e)).push(p.get_id(t)).m_id;
        e = mk_typed_expr_distrib_choice(p, t, e, pos);
        p.set_ast_pexpr(id, e);
        data.push(id);
    } else {
        data.push(p.get_id(e));
    }
    p.check_token_next(get_rparen_tk(), "invalid quoted expression, `)` expected");
    auto r = p.save_pos(mk_pexpr_quote_and_substs(e, /* is_strict */ false), pos);
    p.set_ast_pexpr(data.m_id, r);
    return r;
}

static expr parse_quoted_pexpr(parser & p, unsigned, expr const *, pos_info const & pos) {
    if (p.in_quote())
        return p.parser_error_or_expr({"invalid nested quoted expression", pos});
    parser::quote_scope scope1(p, true, id_behavior::ErrorIfUndef);
    restore_decl_meta_scope scope2;
    expr e = p.parse_expr();
    auto& data = p.new_ast("``()", pos);
    if (p.curr_is_token(get_colon_tk())) {
        p.next();
        expr t = p.parse_expr();
        ast_id id = p.new_ast(get_colon_tk(), p.pos_of(e)).push(p.get_id(e)).push(p.get_id(t)).m_id;
        e = mk_typed_expr_distrib_choice(p, t, e, pos);
        p.set_ast_pexpr(id, e);
        data.push(id);
    } else {
        data.push(p.get_id(e));
    }
    p.check_token_next(get_rparen_tk(), "invalid quoted expression, `)` expected");
    auto r = p.save_pos(mk_pexpr_quote_and_substs(e, /* is_strict */ true), pos);
    p.set_ast_pexpr(data.m_id, r);
    return r;
}

static expr parse_quoted_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    if (p.in_quote())
        return p.parser_error_or_expr({"invalid nested quoted expression", pos});
    auto& data = p.new_ast("`()", pos);
    expr e;
    {
        parser::quote_scope scope1(p, true, id_behavior::ErrorIfUndef);
        restore_decl_meta_scope scope2;
        e = p.parse_expr();
        if (p.curr_is_token(get_colon_tk())) {
            p.next();
            expr t = p.parse_expr();
            ast_id id = p.new_ast(get_colon_tk(), p.pos_of(e)).push(p.get_id(e)).push(p.get_id(t)).m_id;
            e = mk_typed_expr_distrib_choice(p, t, e, pos);
            p.set_ast_pexpr(id, e);
            data.push(id);
        } else {
            data.push(p.get_id(e));
        }
        p.check_token_next(get_rparen_tk(), "invalid quoted expression, `)` expected");
    }
    auto r = p.save_pos(mk_unelaborated_expr_quote(e), pos);
    p.set_ast_pexpr(data.m_id, r);
    return r;
}

static expr parse_antiquote_expr(parser & p, unsigned, expr const *, pos_info const & pos) {
    if (!p.in_quote())
        return p.parser_error_or_expr({"invalid antiquotation, occurs outside of quoted expressions", pos});
    parser::quote_scope scope(p, false);
    expr e = p.parse_expr(get_max_prec());
    ast_id id = p.new_ast("%%", pos).push(p.get_id(e)).m_id;
    e = p.save_pos(mk_antiquote(e), pos);
    p.set_ast_pexpr(id, e);
    return e;
}

static expr parse_quoted_name(parser & p, unsigned, expr const *, pos_info const & pos) {
    bool resolve = false;
    name id;
    auto& data = p.new_ast("`", pos);
    if (p.curr_is_token(get_placeholder_tk())) {
        p.next();
        id = "_";
    } else {
        if (p.curr_is_token(get_backtick_tk())) {
            data.m_type = "``";
            p.next();
            resolve = true;
        }
        if (p.curr_is_keyword() || p.curr_is_command()) {
            if (resolve)
                return p.parser_error_or_expr({"invalid resolved quote symbol, identifier is a keyword/command", pos});
            id = p.get_token_info().token();
            p.next();
        } else {
            id = p.check_id_next("invalid quoted name, identifier expected").second;
        }
    }
    data.m_value = id;
    if (resolve) {
        parser::error_if_undef_scope scope(p);
        bool resolve_only = true;
        expr e = p.id_to_expr(id, p.new_ast("ident", pos, id), resolve_only);
        if (is_constant(e)) {
            id = const_name(e);
        } else if (is_local(e)) {
            id = mlocal_pp_name(e);
        } else if (is_choice(e)) {
            sstream ss;
            ss << "invalid resolved quoted symbol, it is ambiguous, possible interpretations:";
            for (unsigned i = 0; i < get_num_choices(e); i++)
                ss << " " << get_choice(e, i);
            ss << " (solution: use fully qualified names)";
            return p.parser_error_or_expr({ss, pos});
        } else {
            return p.parser_error_or_expr({"invalid quoted symbol, failed to resolve it "
                               "(solution: use `<identifier> to bypass name resolution)", pos});
        }
    }
    lean_assert(id.is_string());
    expr e  = quote(id);
    e = p.rec_save_pos(e, pos);
    p.set_ast_pexpr(data.m_id, e);
    return e;
}

static name * g_anonymous_constructor = nullptr;

expr mk_anonymous_constructor(expr const & e) { return mk_annotation(*g_anonymous_constructor, e); }

bool is_anonymous_constructor(expr const & e) { return is_annotation(e, *g_anonymous_constructor); }

expr const & get_anonymous_constructor_arg(expr const & e) {
    lean_assert(is_anonymous_constructor(e));
    return get_annotation_arg(e);
}

static expr parse_constructor_core(parser & p, pos_info const & pos) {
    buffer<expr> args;
    auto& data = p.new_ast(get_langle_tk(), pos);
    while (!p.curr_is_token(get_rangle_tk())) {
        args.push_back(p.parse_expr());
        data.push(p.get_id(args.back()));
        if (p.curr_is_token(get_comma_tk())) {
            p.next();
        } else {
            break;
        }
    }
    p.check_token_next(get_rangle_tk(), "invalid constructor, `⟩` expected");
    expr fn = p.save_pos(mk_expr_placeholder(), pos);
    expr e = p.save_pos(mk_anonymous_constructor(p.save_pos(mk_app(fn, args), pos)), pos);
    p.set_ast_pexpr(data.m_id, e);
    return e;
}

static expr parse_constructor(parser & p, unsigned, expr const *, pos_info const & pos) {
    return parse_constructor_core(p, pos);
}

static expr parse_lambda_core(parser & p, ast_data & fun, ast_data & bis, pos_info const & pos);

static expr parse_lambda_binder(parser & p, ast_data & fun, ast_data & bis, pos_info const & pos) {
    parser::local_scope scope1(p);
    buffer<expr> locals;
    auto new_env = p.parse_binders(&bis, locals, 0);
    for (expr const & local : locals)
        p.add_local(local);
    parser::local_scope scope2(p, new_env);
    expr body;
    if (p.curr_is_token(get_comma_tk())) {
        p.next();
        body = p.parse_expr();
        fun.push(p.get_id(body));
    } else if (p.curr_is_token(get_langle_tk())) {
        body = parse_lambda_core(p, fun, bis, pos);
    } else {
        p.maybe_throw_error({"invalid lambda expression, ',' or '⟨' expected", p.pos()});
        body = p.parse_expr();
        fun.push(p.get_id(body));
    }
    bool use_cache = false;
    return p.rec_save_pos(Fun(locals, body, use_cache), pos);
}

static name * g_lambda_match_name = nullptr;

static expr parse_lambda_constructor(parser & p, ast_data & fun, ast_data & bis, pos_info const & ini_pos) {
    lean_assert(p.curr_is_token(get_langle_tk()));
    parser::local_scope scope(p);
    auto pos = p.pos();
    p.next();
    buffer<expr> locals;
    expr pattern = p.parse_pattern([&](parser & p) { return parse_constructor_core(p, pos); }, locals);
    bis.push(p.get_id(pattern));
    for (expr const & local : locals)
        p.add_local(local);
    expr body;
    if (p.curr_is_token(get_comma_tk())) {
        p.next();
        body = p.parse_expr();
        fun.push(p.get_id(body));
    } else {
        body = parse_lambda_core(p, fun, bis, ini_pos);
    }
    match_definition_scope match_scope(p.env());
    expr fn  = p.save_pos(mk_local(p.next_name(), *g_lambda_match_name, mk_expr_placeholder(), mk_rec_info(true)), pos);
    expr eqn = Fun(fn, Fun(locals, p.save_pos(mk_equation(p.rec_save_pos(mk_app(fn, pattern), pos), body), pos), p), p);
    equations_header h = mk_match_header(match_scope.get_name(), match_scope.get_actual_name());
    expr x = p.rec_save_pos(mk_local(p.next_name(), "_x", mk_expr_placeholder(), binder_info()), pos);
    bool use_cache = false;
    return p.rec_save_pos(Fun(x, mk_app(mk_equations(h, 1, &eqn), x), use_cache), pos);
}

static expr parse_lambda_core(parser & p, ast_data & fun, ast_data & bis, pos_info const & pos) {
    if (p.curr_is_token(get_langle_tk())) {
        return parse_lambda_constructor(p, fun, bis, pos);
    } else {
        return parse_lambda_binder(p, fun, bis, pos);
    }
}

static expr parse_lambda(parser & p, unsigned, expr const *, pos_info const & pos) {
    auto& bis = p.new_ast("binders", p.pos());
    auto& fun = p.new_ast("fun", pos).push(bis.m_id);
    expr r = parse_lambda_core(p, fun, bis, pos);
    p.set_ast_pexpr(fun.m_id, r);
    return r;
}

static expr parse_assume(parser & p, unsigned, expr const *, pos_info const & pos) {
    ast_id id; expr r;
    if (p.curr_is_token(get_colon_tk())) {
        // anonymous `assume`
        p.next();
        expr prop = p.parse_expr();
        auto& binder = p.new_ast(name("binder").append_after(0U), p.pos())
            .push(0).push(0).push(p.get_id(prop));
        auto& bis = p.new_ast("binders", p.pos()).push(binder.m_id);
        p.check_token_next(get_comma_tk(), "invalid 'assume', ',' expected");
        parser::local_scope scope(p);
        expr l = p.save_pos(mk_local(get_this_tk(), prop), pos);
        p.add_local(l);
        expr body = p.parse_expr();
        id = p.new_ast("assume", pos).push(bis.m_id).push(p.get_id(body)).m_id;
        r = p.save_pos(Fun(l, body, p), pos);
    } else {
        auto& bis = p.new_ast("binders", p.pos());
        auto& fun = p.new_ast("assume", pos).push(bis.m_id);
        id = fun.m_id;
        r = parse_lambda_core(p, fun, bis, pos);
    }
    p.set_ast_pexpr(id, r);
    return r;
}

static void consume_rparen(parser & p) {
    p.check_token_next(get_rparen_tk(), "invalid expression, `)` expected");
}

static name * g_infix_function = nullptr;

bool is_infix_function(expr const & e) {
    return is_annotation(e, *g_infix_function);
}

expr mk_infix_function(expr const & e) {
    return mk_annotation(*g_infix_function, e);
}

/* Check whether notation such as (<) (+ 10) is applicable.
   Like Haskell,
     (<) is notation for (fun x y, x < y)
     (+ 10) is notation for (fun x, x + 10)

   This kind of notation is applicable when
   1- The current token is a keyword.
   2- There is no entry for this token in the nud table
   3- There is an entry for this token in the led table,
      and exactly one Expr transition to an accepting state.

   If the notation is applicable, this function returns the accepting list.
*/
static list<notation::accepting> is_infix_paren_notation(parser & p) {
    if (p.curr_is_keyword() &&
        !p.nud().find(p.get_token_info().value())) {
        list<pair<transition, parse_table>> ts = p.led().find(p.get_token_info().value());
        if (ts && !tail(ts) && head(ts).second.is_accepting()) {
            notation::action const & act = head(ts).first.get_action();
            if (act.kind() == notation::action_kind::Expr) {
                return head(ts).second.is_accepting();
            }
        }
    }
    return list<notation::accepting>();
}

static expr parse_infix_paren(parser & p, list<notation::accepting> const & accs, pos_info const & pos) {
    expr args[2];
    buffer<expr> vars;
    bool fixed_second_arg = false;
    args[0] = mk_local(p.next_name(), "_x", mk_expr_placeholder(), binder_info());
    vars.push_back(args[0]);
    p.next();
    auto& data = p.new_ast(*g_infix_function, pos).push(0);
    if (p.curr_is_token(get_rparen_tk())) {
        data.push(0);
        p.next();
        args[1] = mk_local(p.next_name(), "_y", mk_expr_placeholder(), binder_info());
        vars.push_back(args[1]);
    } else {
        fixed_second_arg = true;
        args[1] = p.parse_expr();
        data.push(p.get_id(args[1]));
        consume_rparen(p);
    }
    buffer<expr> cs;
    for (notation::accepting const & acc : accs) {
        expr r = p.copy_with_new_pos(acc.get_expr(), pos);
        if (!fixed_second_arg && get_app_num_args(r) == 2 && closed(app_fn(app_fn(r))) &&
            is_var(app_arg(app_fn(r)), 1) && is_var(app_arg(r), 0)) {
            /* r is of the form (f #1 #0).
               Thus, we add f to cs instead of (fun x y, f x y) */
            cs.push_back(app_fn(app_fn(r)));
        } else {
            r = p.save_pos(mk_infix_function(Fun(vars, instantiate_rev(r, 2, args), p)), pos);
            cs.push_back(r);
        }
    }
    expr r = p.save_pos(mk_choice(cs.size(), cs.data()), pos);
    lean_assert(data.m_children.size() > 0);
    if (length(accs) > 1) {
        auto& choice = p.new_ast("choice", pos);
        data.m_children[0] = choice.m_id;
        for (auto& a : accs)
            choice.push(p.new_ast(get_notation_tk(), pos, a.get_name()).m_id);
    } else {
        data.m_children[0] = p.new_ast(get_notation_tk(), pos, head(accs).get_name()).m_id;
    }
    p.set_ast_pexpr(data.m_id, r);
    return r;
}

expr parse_lparen(parser & p, unsigned, expr const *, pos_info const & pos) {
    if (auto accs = is_infix_paren_notation(p))
        return parse_infix_paren(p, accs, pos);
    expr e = p.parse_expr();
    if (p.curr_is_token(get_comma_tk())) {
        buffer<expr> args;
        args.push_back(e);
        while (p.curr_is_token(get_comma_tk())) {
            p.next();
            args.push_back(p.parse_expr());
        }
        consume_rparen(p);
        expr r = args.back();
        unsigned i = args.size() - 1;
        while (i > 0) {
            --i;
            r = p.save_pos(mk_app(p.save_pos(mk_constant(get_prod_mk_name()), pos),
                                  args[i], r), pos);
        }
        auto& data = p.new_ast("tuple", pos);
        for (expr& e : args) data.push(p.get_id(e));
        p.set_ast_pexpr(data.m_id, r);
        return r;
    } else if (p.curr_is_token(get_colon_tk())) {
        p.next();
        expr t = p.parse_expr();
        consume_rparen(p);
        ast_id id = p.new_ast(get_colon_tk(), p.pos_of(e)).push(p.get_id(e)).push(p.get_id(t)).m_id;
        e = mk_typed_expr_distrib_choice(p, t, e, pos);
        p.set_ast_pexpr(id, e);
        return e;
    } else {
        consume_rparen(p);
        p.set_ast_pexpr(p.new_ast("(", pos).push(p.get_id(e)).m_id, e);
        return e;
    }
}

static expr parse_lambda_cons(parser & p, unsigned, expr const *, pos_info const & pos) {
    list<pair<transition, parse_table>> ts = p.led().find(get_dcolon_tk());
    if (!ts || tail(ts) || !head(ts).second.is_accepting())
        throw parser_error("invalid '(::)' notation, infix operator '::' has not been defined yet or is the prefix of another notation declaration", pos);
    notation::action const & act = head(ts).first.get_action();
    if (act.kind() != notation::action_kind::Expr)
        throw parser_error("invalid '(::)' notation, declaration for operator '::' is not compatible with the `(::)` syntactic sugar", pos);
    expr args[2];
    buffer<expr> vars;
    args[0] = mk_local(p.next_name(), "_x", mk_expr_placeholder(), binder_info());
    vars.push_back(args[0]);
    args[1] = mk_local(p.next_name(), "_y", mk_expr_placeholder(), binder_info());
    vars.push_back(args[1]);
    buffer<expr> cs;
    auto& accs = head(ts).second.is_accepting();
    for (notation::accepting const & acc : accs) {
        expr r = p.copy_with_new_pos(acc.get_expr(), pos);
        r = p.save_pos(mk_infix_function(Fun(vars, instantiate_rev(r, 2, args), p)), pos);
        cs.push_back(r);
    }
    expr r = p.save_pos(mk_choice(cs.size(), cs.data()), pos);
    auto& data = p.new_ast(*g_infix_function, pos);
    if (length(accs) > 1) {
        auto& choice = p.new_ast("choice", pos);
        data.push(choice.m_id);
        for (auto& a : accs)
            choice.push(p.new_ast(get_notation_tk(), pos, a.get_name()).m_id);
    } else {
        data.push(p.new_ast(get_notation_tk(), pos, head(accs).get_name()).m_id);
    }
    data.push(0);
    p.set_ast_pexpr(data.m_id, r);
    return r;
}

static expr parse_inaccessible(parser & p, unsigned, expr const *, pos_info const & pos) {
    expr e = p.parse_expr();
    if (!p.in_pattern()) {
        p.maybe_throw_error({"inaccesible pattern notation `.(t)` can only be used in patterns", pos});
        return e;
    }
    p.check_token_next(get_rparen_tk(), "invalid inaccesible pattern, `)` expected");
    e = p.save_pos(mk_inaccessible(e), pos);
    p.set_ast_pexpr(p.new_ast(".(", pos).push(p.get_id(e)).m_id, e);
    return e;
}

static expr parse_atomic_inaccessible(parser & p, unsigned, expr const *, pos_info const & pos) {
    if (!p.in_pattern()) {
        return p.parser_error_or_expr({"inaccesible pattern notation `._` can only be used in patterns", pos});
    }
    expr e = p.save_pos(mk_expr_placeholder(), pos);
    ast_id id = p.new_ast("_", pos).m_id;
    p.set_ast_pexpr(id, e);
    e = p.save_pos(mk_inaccessible(e), pos);
    p.set_ast_pexpr(p.new_ast(".(", pos).push(id).m_id, e);
    return e;
}

static name * g_begin_hole = nullptr;
static name * g_end_hole   = nullptr;

expr mk_hole(parser & p, expr const & e, pos_info const & begin_pos, pos_info const & end_pos) {
    return mk_annotation_with_pos(p, *g_begin_hole, mk_annotation_with_pos(p, *g_end_hole, e, end_pos), begin_pos);
}

bool is_hole(expr const & e) {
    return is_annotation(e, *g_begin_hole);
}

std::tuple<expr, optional<pos_info>, optional<pos_info>> get_hole_info(expr const & e) {
    lean_assert(is_hole(e));
    optional<pos_info> begin_pos, end_pos;
    if (get_pos_info_provider()) {
        begin_pos = get_pos_info_provider()->get_pos_info(e);
        end_pos   = get_pos_info_provider()->get_pos_info(get_annotation_arg(e));
    }
    expr args = get_annotation_arg(get_annotation_arg(e));
    return std::make_tuple(args, begin_pos, end_pos);
}

expr update_hole_args(expr const & e, expr const & new_args) {
    lean_assert(is_hole(e));
    return copy_annotations(e, new_args);
}

static expr parse_hole(parser & p, unsigned, expr const *, pos_info const & begin_pos) {
    buffer<expr> ps;
    auto& data = p.new_ast("{!", begin_pos);
    while (!p.curr_is_token(get_rcurlybang_tk())) {
        expr e;
        if (p.in_quote()) {
            e = p.parse_expr();
        } else {
            parser::quote_scope scope(p, false);
            e = p.parse_expr();
        }
        data.push(p.get_id(e));
        ps.push_back(copy_tag(e, mk_pexpr_quote(e)));
        if (!p.curr_is_token(get_comma_tk()))
            break;
        p.next();
    }
    auto end_pos = p.pos();
    p.check_token_next(get_rcurlybang_tk(), "invalid hole, `!}` expected");
    end_pos.second += 2;
    expr r = mk_hole(p, mk_lean_list(ps), begin_pos, end_pos);
    p.set_ast_pexpr(data.m_id, r);
    return r;
}


static expr mk_bin_tree(parser & p, buffer<expr> const & args, unsigned start, unsigned end, pos_info const & pos) {
    lean_assert(start < end);
    lean_assert(end <= args.size());
    if (end == start+1)
        return p.save_pos(mk_app(p.save_pos(mk_constant(get_bin_tree_leaf_name()), pos), args[start]), pos);
    unsigned mid = (start + end)/2;
    expr left  = mk_bin_tree(p, args, start, mid, pos);
    expr right = mk_bin_tree(p, args, mid, end, pos);
    return p.save_pos(mk_app(p.save_pos(mk_constant(get_bin_tree_node_name()), pos),
                             left, right),
                      pos);
}


static expr parse_bin_tree(parser & p, unsigned, expr const *, pos_info const & pos) {
    buffer<expr> es;
    auto& data = p.new_ast("#[", pos);
    while (!p.curr_is_token(get_rbracket_tk())) {
        expr e = p.parse_expr();
        es.push_back(e);
        data.push(p.get_id(e));
        if (!p.curr_is_token(get_comma_tk()))
            break;
        p.next();
    }
    p.check_token_next(get_rbracket_tk(), "invalid `#[...]`, `]` expected");
    expr r;
    if (es.empty()) {
        r = p.save_pos(mk_constant(get_bin_tree_empty_name()), pos);
    } else {
        r = mk_bin_tree(p, es, 0, es.size(), pos);
    }
    p.set_ast_pexpr(data.m_id, r);
    return r;
}

parse_table init_nud_table() {
    action Expr(mk_expr_action());
    action Skip(mk_skip_action());
    action Binders(mk_binders_action());
    expr x0 = mk_var(0);
    parse_table r;
    r = r.add({transition("by", mk_ext_action_core(parse_by))}, x0);
    r = r.add({transition("have", mk_ext_action(parse_have))}, x0);
    r = r.add({transition("assume", mk_ext_action(parse_assume))}, x0);
    r = r.add({transition("show", mk_ext_action(parse_show))}, x0);
    r = r.add({transition("suffices", mk_ext_action(parse_suffices))}, x0);
    r = r.add({transition("if", mk_ext_action(parse_if_then_else))}, x0);
    r = r.add({transition("(", mk_ext_action(parse_lparen))}, x0);
    r = r.add({transition("⟨", mk_ext_action(parse_constructor))}, x0);
    r = r.add({transition("{", mk_ext_action(parse_curly_bracket))}, x0);
    r = r.add({transition("{!", mk_ext_action(parse_hole))}, x0);
    r = r.add({transition(".(", mk_ext_action(parse_inaccessible))}, x0);
    r = r.add({transition("._", mk_ext_action(parse_atomic_inaccessible))}, x0);
    r = r.add({transition("```(", mk_ext_action(parse_lazy_quoted_pexpr))}, x0);
    r = r.add({transition("``(", mk_ext_action(parse_quoted_pexpr))}, x0);
    r = r.add({transition("`(", mk_ext_action(parse_quoted_expr))}, x0);
    r = r.add({transition("`[", mk_ext_action(parse_interactive_tactic_block))}, x0);
    r = r.add({transition("`", mk_ext_action(parse_quoted_name))}, x0);
    r = r.add({transition("%%", mk_ext_action(parse_antiquote_expr))}, x0);
    r = r.add({transition("#[", mk_ext_action(parse_bin_tree))}, x0);
    r = r.add({transition("(:", Expr), transition(":)", mk_ext_action(parse_pattern))}, x0);
    r = r.add({transition("()", mk_ext_action(parse_unit))}, x0);
    r = r.add({transition("(::)", mk_ext_action(parse_lambda_cons))}, x0);
    r = r.add({transition("fun", mk_ext_action(parse_lambda))}, x0);
    r = r.add({transition("Pi", Binders), transition(",", mk_scoped_expr_action(x0, 0, false))}, x0);
    r = r.add({transition("Type", mk_ext_action(parse_Type))}, x0);
    r = r.add({transition("Type*", mk_ext_action(parse_Type_star))}, x0);
    r = r.add({transition("Sort", mk_ext_action(parse_Sort))}, x0);
    r = r.add({transition("Sort*", mk_ext_action(parse_Sort_star))}, x0);
    r = r.add({transition("let", mk_ext_action(parse_let_expr))}, x0);
    r = r.add({transition("calc", mk_ext_action(parse_calc_expr))}, x0);
    r = r.add({transition("@", mk_ext_action(parse_explicit_expr))}, x0);
    r = r.add({transition("@@", mk_ext_action(parse_partial_explicit_expr))}, x0);
    r = r.add({transition("begin", mk_ext_action_core(parse_begin_end))}, x0);
    r = r.add({transition("sorry", mk_ext_action(parse_sorry))}, x0);
    r = r.add({transition("match", mk_ext_action(parse_match))}, x0);
    r = r.add({transition("do", mk_ext_action(parse_do_expr))}, x0);
    return r;
}

static expr parse_field(parser & p, unsigned, expr const * args, pos_info const & pos) {
    try {
        if (p.curr_is_numeral()) {
            ast_id id; unsigned fidx;
            std::tie(id, fidx) = p.parse_small_nat();
            expr r = p.save_pos(mk_field_notation(args[0], fidx), pos);
            p.set_ast_pexpr(p.new_ast("^.", pos).push(p.get_id(args[0])).push(id).m_id, r);
            return r;
        } else {
            ast_id id; name field;
            std::tie(id, field) = p.check_id_next("identifier or numeral expected");
            expr r = p.save_pos(mk_field_notation(args[0], field), pos);
            p.set_ast_pexpr(p.new_ast("^.", pos).push(p.get_id(args[0])).push(id).m_id, r);
            return r;
        }
    } catch (break_at_pos_exception & ex) {
        if (!p.get_complete()) {
            // info is stored at position of notation token
            ex.m_token_info.m_pos = pos;
        }
        expr lhs = args[0];
        expr lhs_type;
        try {
            metavar_context mctx;
            bool check_unassigned = false;
            lhs = p.elaborate({}, mctx, lhs, check_unassigned).first;
            type_checker tc(p.env(), true, false);
            lhs_type = tc.infer(lhs);
        } catch (exception &) {
            /* failed to elaborate or infer type */
            throw ex;
        }
        expr fn = get_app_fn(lhs_type);
        if (is_constant(fn)) {
            ex.m_token_info.m_context = break_at_pos_exception::token_context::field;
            ex.m_token_info.m_param   = const_name(fn);
        }
        throw;
    }
}

static name * g_arrow_binder = nullptr;

parse_table init_led_table() {
    parse_table r(false);
    r = r.add({transition("->", mk_expr_action(get_arrow_prec()-1))}, mk_pi(*g_arrow_binder, Var(1), Var(1), binder_info()));
    r = r.add({transition("^.", mk_ext_action(parse_field))}, Var(0));
    return r;
}

static parse_table * g_nud_table = nullptr;
static parse_table * g_led_table = nullptr;

parse_table get_builtin_nud_table() {
    return *g_nud_table;
}

parse_table get_builtin_led_table() {
    return *g_led_table;
}

void initialize_builtin_exprs() {
    g_no_universe_annotation = new name("no_univ");
    register_annotation(*g_no_universe_annotation);

    g_do_failure_eq     = new name("do_failure_eq");
    register_annotation(*g_do_failure_eq);

    g_infix_function    = new name("infix_fn");
    register_annotation(*g_infix_function);

    g_begin_hole = new name("begin_hole");
    register_annotation(*g_begin_hole);

    g_end_hole = new name("end_hole");
    register_annotation(*g_end_hole);

    g_arrow_binder = new name("ᾰ");

    g_not               = new expr(mk_constant(get_not_name()));
    g_nud_table         = new parse_table();
    *g_nud_table        = init_nud_table();
    g_led_table         = new parse_table();
    *g_led_table        = init_led_table();
    g_do_match_name     = new name("_do_match");
    g_let_match_name    = new name("_let_match");
    g_lambda_match_name = new name("_fun_match");

    g_parser_checkpoint_have = new name{"parser", "checkpoint_have"};
    register_bool_option(*g_parser_checkpoint_have, LEAN_DEFAULT_PARSER_CHECKPOINT_HAVE,
                         "(parser) introduces a checkpoint on have-expressions, checkpoints are like Prolog-cuts");

    g_anonymous_constructor = new name("anonymous_constructor");
    register_annotation(*g_anonymous_constructor);
}

void finalize_builtin_exprs() {
    delete g_begin_hole;
    delete g_end_hole;
    delete g_do_failure_eq;
    delete g_infix_function;
    delete g_arrow_binder;
    delete g_led_table;
    delete g_nud_table;
    delete g_not;
    delete g_do_match_name;
    delete g_let_match_name;
    delete g_lambda_match_name;
    delete g_parser_checkpoint_have;
    delete g_anonymous_constructor;
    delete g_no_universe_annotation;
}
}
