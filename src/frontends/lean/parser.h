/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <utility>
#include <vector>
#include "util/flet.h"
#include "util/name_map.h"
#include "util/exception.h"
#include "util/task.h"
#include "kernel/environment.h"
#include "kernel/expr_maps.h"
#include "library/util.h"
#include "library/module.h"
#include "library/abstract_parser.h"
#include "library/io_state.h"
#include "library/io_state_stream.h"
#include "library/message_builder.h"
#include "library/tactic/tactic_log.h"
#include "library/tactic/tactic_state.h"
#include "frontends/lean/parser_state.h"
#include "frontends/lean/local_decls.h"
#include "frontends/lean/local_level_decls.h"
#include "frontends/lean/parser_config.h"
#include "frontends/lean/local_context_adapter.h"
#include "frontends/lean/decl_util.h"

namespace lean {
struct interrupt_parser {};
typedef environment             local_environment;
class metavar_context;
class local_context_adapter;
class scope_message_context;

#define AST_TOP_ID 1

class parser_info {
protected:
    environment             m_env;
    local_expr_decls        m_local_decls;
    name_set                m_level_variables;
    name_set                m_variables; // subset of m_local_decls that is marked as variables
    local_level_decls       m_local_level_decls;
    bool                    m_has_params; // true context context contains parameters
    name_set                m_include_vars; // subset of m_local_decls that is marked as include
    bool                    m_in_quote;
    bool                    m_in_pattern;
    io_state                m_ios;
    parser_scope_stack      m_parser_scope_stack;
    unsigned                m_next_inst_idx;
    bool                    m_show_errors;
    // profiling
    bool                   m_profile;

    // If the following flag is true we do not raise error messages
    // noncomputable definitions not tagged as noncomputable.
    bool                   m_ignore_noncomputable;

    // error recovery
    bool                   m_error_recovery = true;

public:
    parser_info(environment const & env, io_state const & ios) :
       m_env(env), m_ios(ios) {}
    bool is_local_decl_user_name(expr const & l) const { return is_local(l) && m_local_decls.contains(mlocal_pp_name(l)); }
    bool is_local_decl(expr const & l);
    bool is_local_level_variable(name const & n) const { return m_level_variables.contains(n); }
    bool is_local_variable(expr const & e) const { return m_variables.contains(mlocal_name(e)); }
    bool is_local_variable_user_name(name const & n) const {
        if (expr const * d = m_local_decls.find(n))
            return is_local(*d) && m_variables.contains(mlocal_name(*d));
        else
            return false;
    }
    void clear_expr_locals();
    bool has_locals() const { return !m_local_decls.empty() || !m_local_level_decls.empty(); }
    void add_local_level(name const & n, level const & l, bool is_variable = false);
    void add_local_expr(name const & n, expr const & p, bool is_variable = false);
    environment add_local_ref(environment const & env, name const & n, expr const & ref);
    void add_variable(name const & n, expr const & p);
    void add_parameter(name const & n, expr const & p);
    void add_local(expr const & p, bool is_variable = false) {
        return add_local_expr(mlocal_pp_name(p), p, is_variable); }
    bool has_params() const { return m_has_params; }
    /** \brief Update binder information for the section parameter n, return true if success, and false if n is not a section parameter. */
    bool update_local_binder_info(name const & n, binder_info const & bi);
    void include_variable(name const & n) { m_include_vars.insert(n); }
    void omit_variable(name const & n) { m_include_vars.erase(n); }
    bool is_include_variable(name const & n) const { return m_include_vars.contains(n); }
    void get_include_variables(buffer<expr> & vars) const;
    void get_include_var_names(buffer<name> & vars) const;
    void get_available_include_var_names(buffer<expr> & vars) const;
    /** \brief Position of the local level declaration named \c n in the sequence of local level decls. */
    unsigned get_local_level_index(name const & n) const { return m_local_level_decls.find_idx(n); }
    bool is_local_level(name const & n) const { return m_local_level_decls.contains(n); }
    /** \brief Position of the local declaration named \c n in the sequence of local decls. */
    unsigned get_local_index(name const & n) const;
    unsigned get_local_index(expr const & e) const { return get_local_index(mlocal_pp_name(e)); }
    /** \brief Return the local parameter named \c n */
    expr const * get_local(name const & n) const { return m_local_decls.find(n); }
    /** \brief Return local declarations as a list of local constants. */
    list<expr> locals_to_context() const;
    /** \brief Return all local declarations and aliases */
    list<pair<name, expr>> const & get_local_entries() const { return m_local_decls.get_entries(); }
    virtual pos_info pos() const = 0;
    virtual void maybe_throw_error(parser_error && err) = 0;

    environment const & env() const { return m_env; }
    void set_env(environment const & env) { m_env = env; }
    io_state const & ios() const { return m_ios; }

    struct local_scope {
        parser_info & m_p; environment m_env;
        local_scope(parser_info & p, bool save_options = false);
        local_scope(parser_info & p, environment const & env);
        local_scope(parser_info & p, optional<environment> const & env);
        ~local_scope();
    };

    bool has_local_scopes() const { return !is_nil(m_parser_scope_stack); }
    void push_local_scope(bool save_options = true);
    void pop_local_scope();
protected:
    parser_scope mk_parser_scope(optional<options> const & opts = optional<options>());
    void restore_parser_scope(parser_scope const & s);

    virtual std::tuple<expr, expr, name> parse_definition(ast_data * parent, buffer<name> & lp_names, buffer<expr> & params,
                                                          bool is_example, bool is_instance, bool, bool) = 0;

    friend environment single_definition_cmd_core(parser_info & p, decl_cmd_kind kind, ast_data * parent, cmd_meta meta);
public:
    void updt_options();
    options get_options() const { return m_ios.get_options(); }
    template<typename T> void set_option(name const & n, T const & v) { m_ios.set_option(n, v); }
    virtual expr save_pos(expr const & e, pos_info p) = 0;
    virtual expr rec_save_pos(expr const & e, pos_info p) = 0;
    virtual expr rec_save_pos(expr const & e, optional<pos_info> p) = 0;
    virtual optional<pos_info> get_pos_info(expr const & e) const = 0;
    virtual message_builder mk_message(pos_info const &p, message_severity severity) const = 0;
    virtual message_builder mk_message(message_severity severity) const = 0;
    bool ignore_noncomputable() const { return m_ignore_noncomputable; }
    void set_ignore_noncomputable() { m_ignore_noncomputable = true; }
    virtual char const * get_file_name() const = 0;
    virtual pos_info cmd_pos() const = 0;
    virtual optional<pos_info> const & get_break_at_pos() const = 0;
    virtual parser_pos_provider get_parser_pos_provider(pos_info const & some_pos) const = 0;
    virtual std::shared_ptr<tactic_log> get_tactic_log() { return nullptr; }
    expr mk_sorry(pos_info const & p, bool synthetic = false);
    bool has_error_recovery() const { return m_error_recovery; }
};

typedef rb_map<unsigned, ast_id, unsigned_cmp> tag_ast_table;

class parser : public abstract_parser, public parser_info {
    name_generator          m_ngen;
    bool                    m_use_exceptions;
    module_loader           m_import_fn;
    std::string             m_file_name;
    scanner                 m_scanner;
    token_kind              m_curr;
    bool                    m_imports_parsed = false;
    bool                    m_scanner_inited = false;
    parser_scope_stack      m_quote_stack;
    pos_info                m_last_cmd_pos;
    unsigned                m_next_tag_idx;
    ast_id                  m_vm_parser_ast_id = 0;
    pos_info_table          m_pos_table;
    tag_ast_table           m_tag_ast_table;
    std::vector<ast_data*>  m_ast;
    bool                    m_ast_invalid = false;
    ast_id                  m_commands = 0;
    std::shared_ptr<tactic_log> m_tactic_log;
    // By default, when the parser finds a unknown identifier, it signs an error.
    // When the following flag is true, it creates a constant.
    // This flag is when we are trying to parse mutually recursive declarations.
    id_behavior             m_id_behavior;

    optional<pos_info>      m_break_at_pos;
    // auto completing
    bool                    m_complete{false};

    bool                   m_error_since_last_cmd = false;
    pos_info               m_last_recovered_error_pos {0, 0};
    optional<pos_info>     m_backtracking_pos;

    void sync_command();

    tag get_tag(expr e);

    unsigned curr_level_lbp() const;
    pair<ast_id, level> parse_max_imax(bool is_max);
    pair<ast_id, level> parse_level_id();
    pair<ast_id, level> parse_level_nud();
    pair<ast_id, level> parse_level_led(pair<ast_id, level> left);

    ast_id parse_mod_doc_block();

    void process_imports(ast_data * parent);
    void process_postponed(buffer<expr> const & args, bool is_left, buffer<notation::action_kind> const & kinds,
                           buffer<list<expr>> const & nargs, buffer<expr> const & ps, buffer<pair<unsigned, pos_info>> const & scoped_info,
                           list<notation::action> const & postponed, pos_info const & p, buffer<expr> & new_args);
    expr parse_notation(parse_table t, expr * left);
    expr parse_nud_notation();
    expr parse_led_notation(expr left);
    expr parse_inaccessible();
    expr parse_placeholder();
    // expr parse_anonymous_var_pattern();
    expr parse_nud();
    bool curr_starts_expr();
    expr parse_numeral_expr(bool user_notation = true);
    expr parse_decimal_expr();
    expr parse_string_expr();
    expr parse_char_expr();
    pair<ast_id, expr> parse_inst_implicit_decl();
    void parse_inst_implicit_decl(ast_data * parent, buffer<expr> & r);
    expr parse_binder_core(binder_info const & bi, unsigned rbp);
    ast_id parse_binder_collection(buffer<pair<pos_info, name>> const & names, binder_info const & bi, buffer<expr> & r);
    ast_id parse_binder_block(buffer<expr> & r, binder_info const & bi, unsigned rbp, bool allow_default);
    struct parse_binders_config {
        /* (input) If m_allow_empty is true, then parse_binders will succeed even if not binder is parsed. */
        bool     m_allow_empty{false};
        /* (input) right binding power */
        unsigned m_rbp{0};
        /* (input) If m_simple_only, then binder modifiers '{', '[' and '⦃' are not allowed. */
        bool     m_simple_only{false};
        /* (input) If true, it will allow binders of the form (x : T := v), and they will be converted
           into (x : opt_param T v) */
        bool     m_allow_default{false};
        /* (input) If true, then all binders must be surrounded with some kind of bracket. (e.g., '()', '{}', '[]').
           We use this feature when parsing examples/definitions/theorems. The goal is to avoid counter-intuitive
           declarations such as:

              example p : false := trivial
              def main proof : false := trivial

           which would be parsed as

              example (p : false) : _ := trivial

              def main (proof : false) : _ := trivial

           where `_` in both cases is elaborated into `true`. This issue was raised by @gebner in the slack channel.


           Remark: we still want implicit delimiters for lambda/pi expressions. That is, we want to
           write

               fun x : t, s
           or
               fun x, s

           instead of

               fun (x : t), s
        */
        bool     m_explicit_delimiters{false};
        /* (input and output)
          If m_infer_kind != nullptr, then a sequence of binders can be prefixed with '{}' or '()'
          Moreover, *m_infer_kind will be updated with

          - implicit_infer_kind::None if prefix is '()'
          - implicit_infer_kind::RelaxedImplicit if prefix is '{}'
          - implicit_infer_kind::Implicit, if prefix is '[]'.

          The default is `RelaxedImplicit` */
        implicit_infer_kind * m_infer_kind{nullptr};
        /* (output) The AST ID associated to the m_infer_kind */
        ast_id * m_infer_kind_id{nullptr};
        /* (output) It is set to true if the last binder is surrounded
           with some kind of bracket (e.g., '()', '{}', '[]'). */
        bool     m_last_block_delimited{false};
        /* (output) If m_nentries != nullptr, then local notation declarations are stored here */
        buffer<notation_entry> * m_nentries{nullptr};
    };
    void parse_binders_core(ast_data * parent, buffer<expr> & r, parse_binders_config & cfg);
    local_environment parse_binders(ast_data * parent, buffer<expr> & r, parse_binders_config & cfg);
    ast_id parse_local_notation_decl(buffer<notation_entry> * entries);

    std::tuple<ast_id, optional<name>, expr> parse_id_tk_expr(name const & tk, unsigned rbp);

    friend environment section_cmd(parser & p, ast_id &);
    friend environment namespace_cmd(parser & p, ast_id &);
    friend environment end_scoped_cmd(parser & p, ast_id &);

    std::shared_ptr<snapshot> mk_snapshot();

    optional<expr> resolve_local(name const & id, ast_data & id_data, pos_info const & p, list<name> const & extra_locals,
                                 bool allow_field_notation = true);

    friend class module_parser;
    friend class patexpr_to_expr_fn;

    struct backtracking_exception {};
    flet<optional<pos_info>> backtracking_scope() {
        return flet<optional<pos_info>>(m_backtracking_pos, optional<pos_info>(pos()));
    }
    bool consumed_input() {
        return *m_backtracking_pos != pos();
    }

public:
    parser(environment const & env, io_state const & ios,
           module_loader const & import_fn,
           std::istream & strm, std::string const & file_name,
           bool use_exceptions = false);
    parser(parser const &) = delete;
    ~parser();

    void init_scanner();

    ast_data & new_ast(name type, pos_info start, name value = {});
    void finalize_ast(ast_id id, expr const & e);
    bool is_ast_invalid() { return m_ast_invalid; }
    void set_ast_expr(ast_id id, expr e);
    ast_data & get_ast(ast_id id) { return *m_ast[id]; }
    ast_id get_id(expr const & e) const;
    ast_data & expr_ast(expr const & e) { return get_ast(get_id(e)); }
    const char * ast_string(ast_id id) const { return m_ast[id]->m_value.get_string(); }
    pos_info ast_pos(ast_id id) const { return m_ast[id]->m_start; }
    void push_from_vm_parse(ast_id id) { if (m_vm_parser_ast_id) get_ast(m_vm_parser_ast_id).push(id); }
    ast_id get_vm_parse_parent() { return m_vm_parser_ast_id; }
    ast_id set_vm_parse_parent(ast_id id) {
        auto old = m_vm_parser_ast_id;
        m_vm_parser_ast_id = id;
        return old;
    }
    ast_data & new_modifiers(cmd_meta & meta);
    friend void export_ast(parser const &);

    void from_snapshot(snapshot const & snap);

    name next_name() { return m_ngen.next(); }

    void set_break_at_pos(pos_info const & pos) { m_break_at_pos = some(pos); }
    optional<pos_info> const & get_break_at_pos() const override { return m_break_at_pos; }
    template <class T>
    T without_break_at_pos(std::function<T()> const & f) {
        flet<optional<pos_info>> l(m_break_at_pos, {});
        return f();
    }
    template <class T>
    pair<T, pos_info> with_input(std::istream & input, std::function<T()> const & f) {
        flet<token_kind> l(m_curr, token_kind::Eof);
        flet<scanner> l1(m_scanner, scanner(input, m_scanner.get_stream_name().c_str()));
        m_curr = m_scanner.scan(m_env);
        T t = f();
        return {t, pos()};
    }
    bool get_complete() { return m_complete; }
    void set_complete(bool complete) { m_complete = complete; }
    /** \brief Throw \c break_at_pos_exception with given context if \c m_break_at_pos is inside current token. */
    void check_break_at_pos(break_at_pos_exception::token_context ctxt = break_at_pos_exception::token_context::none);
    /** \brief Throw \c break_at_pos_exception with empty token and given context if \c m_break_at_pos is before current
        position. */
    void check_break_before(break_at_pos_exception::token_context ctxt = break_at_pos_exception::token_context::none);

    bool in_pattern() const { return m_in_pattern; }

    name mk_anonymous_inst_name();

    unsigned curr_lbp() const;

    cmd_table const & cmds() const { return get_cmd_table(env()); }

    message_builder mk_message(pos_info const & p, message_severity severity) const override;
    message_builder mk_message(pos_info const & start_pos, pos_info const & end_pos, message_severity severity) const;
    message_builder mk_message(message_severity severity) const override;

    local_level_decls const & get_local_level_decls() const { return m_local_level_decls; }
    local_expr_decls const & get_local_expr_decls() const { return m_local_decls; }

    /** \brief Return the current position information */
    virtual pos_info pos() const override final { return m_scanner.get_pos_info(); }
    pos_info end_pos() const { return m_scanner.get_last_end_pos_info(); }
    virtual expr save_pos(expr const & e, pos_info p) override final;
    expr rec_save_pos(expr const & e, pos_info p) override final;
    expr rec_save_pos(expr const & e, optional<pos_info> p) override final { return p ? rec_save_pos(e, *p) : e; }
    expr update_pos(expr e, pos_info p);
    void erase_pos(expr const & e);
    pos_info pos_of(expr const & e, pos_info default_pos) const;
    pos_info pos_of(expr const & e) const { return pos_of(e, pos()); }
    pos_info cmd_pos() const override { return m_last_cmd_pos; }

    parser_pos_provider get_parser_pos_provider(pos_info const & some_pos) const override {
        return parser_pos_provider(m_pos_table, m_file_name, some_pos, m_next_tag_idx);
    }

    std::shared_ptr<tactic_log> get_tactic_log() override;

    expr mk_app(expr fn, expr arg, pos_info const & p);
    expr mk_app(expr fn, buffer<expr> const & args, pos_info const & p);
    expr mk_app(std::initializer_list<expr> const & args, pos_info const & p);

    parse_table const & nud() const { return get_nud_table(env()); }
    parse_table const & led() const { return get_led_table(env()); }
    expr copy_with_new_pos(expr const & e, pos_info p);

    /** \brief Read the next token. */
    void scan();
    /** \brief Return the current token */
    token_kind curr() const { return m_curr; }
    /** \brief Return true iff the current token is an identifier */
    bool curr_is_identifier() const { return curr() == token_kind::Identifier; }
    /** \brief Return true iff the current token is a numeral */
    virtual bool curr_is_numeral() const final override { return curr() == token_kind::Numeral; }
    bool curr_is_decimal() const { return curr() == token_kind::Decimal; }
    /** \brief Return true iff the current token is a string */
    bool curr_is_string() const { return curr() == token_kind::String; }
    /** \brief Return true iff the current token is a keyword */
    bool curr_is_keyword() const { return curr() == token_kind::Keyword; }
    /** \brief Return true iff the current token is a keyword */
    bool curr_is_command() const { return curr() == token_kind::CommandKeyword; }
    /** \brief Return true iff the current token is EOF */
    bool curr_is_eof() const { return curr() == token_kind::Eof; }
    /** \brief Return true iff the current token is a keyword */
    bool curr_is_quoted_symbol() const { return curr() == token_kind::QuotedSymbol; }
    /** \brief Return true iff the current token is a keyword named \c tk or an identifier named \c tk */
    bool curr_is_token_or_id(name const & tk) const;
    /** \brief Return true iff the current token is a command, EOF, period or script block */
    bool curr_is_command_like() const;
    /** \brief Read the next token if the current one is not End-of-file. */
    virtual void next() override final { if (m_curr != token_kind::Eof) scan(); }
    /** \brief Return true iff the current token is a keyword (or command keyword) named \c tk */
    virtual bool curr_is_token(name const & tk) const override final;

    /** \brief Returns the n-th token ahead, where the 0th one is the next one (after \c curr()). */
    token_kind ahead(int n = 0);
    /** \brief Lookahead version of \c curr_is_token. See \c ahead(). */
    bool ahead_is_token(name const & tk, int n = 0);

    /** \brief Check current token, and move to next characther, throw exception if current token is not \c tk.  Returns true if succesful. */
    bool check_token_next(name const & tk, char const * msg);
    void check_token_or_id_next(name const & tk, char const * msg);
    /** \brief Check if the current token is an identifier, if it is return it and move to next token,
        otherwise throw an exception. */
    pair<ast_id, name> check_id_next(char const * msg, break_at_pos_exception::token_context ctxt =
            break_at_pos_exception::token_context::none);
    void check_not_internal(name const & n, pos_info const & pos);
    /** \brief Similar to check_id_next, but also ensures the identifier is *not* an internal/reserved name. */
    pair<ast_id, name> check_decl_id_next(char const * msg, break_at_pos_exception::token_context ctxt =
            break_at_pos_exception::token_context::none);
    /** \brief Check if the current token is an atomic identifier, if it is, return it and move to next token,
        otherwise throw an exception. */
    pair<ast_id, name> check_atomic_id_next(char const * msg);
    pair<ast_id, name> check_atomic_decl_id_next(char const * msg);
    list<name> to_constants(name const & id, char const * msg, pos_info const & p) const;
    name to_constant(name const & id, char const * msg, pos_info const & p);
    /** \brief Check if the current token is a constant, if it is, return it and move to next token, otherwise throw an exception. */
    pair<ast_id, name> check_constant_next(char const * msg);

    mpq const & get_num_val() const { return m_scanner.get_num_val(); }
    name const & get_name_val() const { return m_scanner.get_name_val(); }
    std::string const & get_str_val() const { return m_scanner.get_str_val(); }
    token_info const & get_token_info() const { return m_scanner.get_token_info(); }
    std::string const & get_stream_name() const { return m_scanner.get_stream_name(); }

    unsigned get_small_nat();
    virtual pair<ast_id, unsigned> parse_small_nat() override final;
    virtual pair<ast_id, std::string> parse_string_lit() override final;
    pair<ast_id, double> parse_double();

    /** \brief Parses a documentation block (`/-- TEXT -/`). For example, `/-- Doc\ndoc -/` returns " Doc\ndoc ". */
    pair<ast_id, std::string> parse_doc_block();

    ast_id parse_local_notation_decl() { return parse_local_notation_decl(nullptr); }

    pair<ast_id, level> parse_level(unsigned rbp = 0);

    expr parse_binder(unsigned rbp);

    local_environment parse_binders(ast_data * parent, buffer<expr> & r, bool & last_block_delimited) {
        parse_binders_config cfg;
        auto new_env = parse_binders(parent, r, cfg);
        last_block_delimited = cfg.m_last_block_delimited;
        return new_env;
    }

    local_environment parse_binders(ast_data * parent, buffer<expr> & r, unsigned rbp, bool allow_default = false) {
        parse_binders_config cfg;
        cfg.m_rbp           = rbp;
        cfg.m_allow_default = allow_default;
        return parse_binders(parent, r, cfg);
    }

    void parse_simple_binders(ast_data * parent, buffer<expr> & r, unsigned rbp) {
        parse_binders_config cfg;
        cfg.m_simple_only = true;
        cfg.m_rbp         = rbp;
        parse_binders(parent, r, cfg);
    }

    local_environment parse_optional_binders(ast_data * parent, buffer<expr> & r, bool allow_default = false, bool explicit_delimiters = false) {
        parse_binders_config cfg;
        cfg.m_allow_empty         = true;
        cfg.m_allow_default       = allow_default;
        cfg.m_explicit_delimiters = explicit_delimiters;
        return parse_binders(parent, r, cfg);
    }

    local_environment parse_optional_binders(ast_data * parent, buffer<expr> & r, ast_id & kind_id, implicit_infer_kind & kind) {
        parse_binders_config cfg;
        cfg.m_allow_empty   = true;
        cfg.m_infer_kind    = &kind;
        cfg.m_infer_kind_id = &kind_id;
        return parse_binders(parent, r, cfg);
    }

    local_environment parse_binders(ast_data * parent, buffer<expr> & r, buffer<notation_entry> & nentries) {
        parse_binders_config cfg;
        cfg.m_nentries = &nentries;
        return parse_binders(parent, r, cfg);
    }

    optional<binder_info> parse_optional_binder_info(bool simple_only = false);

    binder_info parse_binder_info(bool simple_only = false);
    void parse_close_binder_info(optional<binder_info> const & bi);
    void parse_close_binder_info(binder_info const & bi) { return parse_close_binder_info(optional<binder_info>(bi)); }

    /** \brief Convert an identifier into an expression (constant or local constant) based on the current scope */
    expr id_to_expr(name const & id, ast_data & data,
                    bool resolve_only = false, bool allow_field_notation = true,
                    list<name> const & extra_locals = list<name>());

    /** Always parses an expression.  Returns a synthetic sorry even if no input is consumed. */
    expr parse_expr(unsigned rbp = 0);
    /** Tries to parse an expression, or else consumes no input. */
    optional<expr> maybe_parse_expr(unsigned rbp = 0);
    /** Tries to parse a pattern in equation-based specifications,
        or else consumes no input. */
    optional<expr> maybe_parse_pattern(unsigned rbp);
    /** \brief Parse an (optionally) qualified expression.
        If the input is of the form <id> : <expr>, then return the pair (some(id), expr).
        Otherwise, parse the next expression and return (none, expr). */
    std::tuple<ast_id, optional<name>, expr> parse_qualified_expr(unsigned rbp = 0);
    /** \brief If the input is of the form <id> := <expr>, then return the pair (some(id), expr).
        Otherwise, parse the next expression and return (none, expr). */
    std::tuple<ast_id, optional<name>, expr> parse_optional_assignment(unsigned rbp = 0);

    /** \brief Parse a pattern or expression */
    expr parse_pattern_or_expr(unsigned rbp = 0);
    /** \brief Convert an expression parsed using parse_pattern_or_expr into a pattern.
        The new local constants declared by the pattern are stored at new_locals.

        If skip_main_fn == true, then in the top-level application (f ...), the function f
        is not processed. */
    expr patexpr_to_pattern(expr const & pat_or_expr, bool skip_main_fn, buffer<expr> & new_locals);
    /** \brief Convert an expression parsed using parse_pattern_or_expr into a regular term. */
    expr patexpr_to_expr(expr const & pat_or_expr);
    expr patexpr_to_expr_core(expr const & pat_or_expr);
    expr parse_pattern(buffer<expr> & new_locals, unsigned rbp = 0) {
        return patexpr_to_pattern(parse_pattern_or_expr(rbp), false, new_locals);
    }
    /* \brief Set pattern mode, and invoke fn. The new locals are stored in new_locals */
    expr parse_pattern(std::function<expr(parser &)> const & fn, buffer<expr> & new_locals);

    expr parse_id(bool allow_field_notation = true);

    expr parse_led(expr left);
    expr parse_led_loop(expr left, unsigned rbp);
    expr parse_scoped_expr(unsigned num_params, expr const * ps, local_environment const & lenv, unsigned rbp = 0);
    expr parse_scoped_expr(buffer<expr> const & ps, local_environment const & lenv, unsigned rbp = 0) {
        return parse_scoped_expr(ps.size(), ps.data(), lenv, rbp);
    }
    expr parse_scoped_expr(unsigned num_params, expr const * ps, unsigned rbp = 0) {
        return parse_scoped_expr(num_params, ps, local_environment(m_env), rbp);
    }
    expr parse_scoped_expr(buffer<expr> const & ps, unsigned rbp = 0) { return parse_scoped_expr(ps.size(), ps.data(), rbp); }
    expr parse_expr_with_env(local_environment const & lenv, unsigned rbp = 0);

    bool parse_command_like(ast_data * parent = nullptr);
    ast_id parse_command(cmd_meta const & meta);
    bool parse_imports(unsigned & fingerprint, ast_data * parent, std::vector<module_name> &);
    bool imports_parsed() const { return m_imports_parsed; }

    struct quote_scope {
        parser &    m_p;
        id_behavior m_id_behavior;
        bool        m_old_in_quote;
        bool        m_in_quote;
        bool        m_saved_in_pattern;
        quote_scope(parser & p, bool q, id_behavior i = id_behavior::AssumeLocalIfNotLocal);
        ~quote_scope();
    };

    bool in_quote() const { return m_in_quote; }

    void maybe_throw_error(parser_error && err) override;
    pair<ast_id, level> parser_error_or_level(parser_error && err);
    expr parser_error_or_expr(parser_error && err);
    void throw_invalid_open_binder(pos_info const & pos);

    flet<bool> error_recovery_scope(bool enable_recovery) {
        return flet<bool>(m_error_recovery, enable_recovery);
    }
    flet<bool> no_error_recovery_scope() { return error_recovery_scope(false); }
    flet<bool> no_error_recovery_scope_if(bool cond) {
        return error_recovery_scope(m_error_recovery && !cond);
    }

    /* This is the default mode. We also use it when converting a pre-term that can be a pattern_or_expression
       into an expression.

       \remark By default, when the parser finds a unknown identifier, it signs an error. */
    struct error_if_undef_scope : public flet<id_behavior> { error_if_undef_scope(parser & p); };
    /* We use this mode when parsing patterns (and a pre-term that can be a pattern or expression). */
    struct all_id_local_scope : public flet<id_behavior> { all_id_local_scope(parser & p); };
    /* We use this mode when converting a pre-term that can be a pattern_or_expression into a pattern. */
    struct undef_id_to_local_scope : public flet<id_behavior> { undef_id_to_local_scope(parser &); };

private:
    pair<expr, level_param_names> elaborate(name const & decl_name, metavar_context & mctx, local_context_adapter const & adapter,
                                            expr const & e, bool check_unassigned = true, bool freeze_instances = true);

public:
    local_context_adapter mk_local_context_adapter() { return local_context_adapter(m_local_decls); }
    pair<expr, level_param_names> elaborate(name const & decl_name, metavar_context & mctx, expr const & e, bool check_unassigned = true, bool freeze_instances = true);
    pair<expr, level_param_names> elaborate(name const & decl_name, metavar_context & mctx, list<expr> const & lctx, expr const & e, bool check_unassigned, bool freeze_instances);
    pair<expr, level_param_names> elaborate(name const & decl_name, list<expr> const & ctx, expr const & e);
    pair<expr, level_param_names> elaborate_type(name const & decl_name, list<expr> const & lctx, expr const & e, bool freeze_instances = true);
    /* Elaborate \c e as a type using the given metavariable context, and using m_local_decls as the local context */
    pair<expr, level_param_names> elaborate_type(name const & decl_name, metavar_context & mctx, expr const & e, bool freeze_instances = true);

    /** return true iff profiling is enabled */
    bool profiling() const { return m_profile; }

    void get_imports(std::vector<module_name> &);

    class in_notation_ctx {
        scanner::in_notation_ctx m_ctx;
    public:
        in_notation_ctx(parser & p):m_ctx(p.m_scanner) {}
    };

    bool in_notation() const { return m_scanner.in_notation(); }

public:
    /* pos_info_provider API */
    virtual optional<pos_info> get_pos_info(expr const & e) const override;
    virtual pos_info get_some_pos() const override;
    virtual char const * get_file_name() const override;

protected:
    virtual std::tuple<expr, expr, name> parse_definition(ast_data * parent, buffer<name> & lp_names, buffer<expr> & params,
                                                          bool is_example, bool is_instance, bool, bool) override;
};

bool parse_commands(environment & env, io_state & ios, char const * fname);

class dummy_def_parser : public parser_info {
public:
  bool            m_ignore_noncomputable;
  pos_info        m_pos;
  std::string     m_file_name;
  name            m_name;
  buffer<name>    m_lp_params;
  buffer<expr>    m_params;
  expr            m_type;
  buffer<pair<buffer<expr>, expr>> m_val;
  optional<expr>  m_wf_tac;
  optional<pos_info> m_break_at_pos;
public:
  dummy_def_parser(environment const & env, options const & opts) :
    parser_info(env, io_state(io_state(), opts))
      { m_error_recovery = false; }
  char const * get_file_name() const override { return m_file_name.c_str(); }
  bool ignore_noncomputable() const { return m_ignore_noncomputable; }
  options get_options() const { return m_ios.get_options(); }
  message_builder mk_message(pos_info const &p, message_severity severity) const override {
    std::shared_ptr<abstract_type_context> tc = std::make_shared<type_context_old>(m_env, get_options());
    return message_builder(tc, m_env, m_ios, get_file_name(), p, severity); }
  message_builder mk_message(message_severity severity) const override {
    return mk_message(pos(), severity); }
  pos_info pos() const override { return m_pos; }
  pos_info cmd_pos() const override { return m_pos; }
  environment const & env() const { return m_env; }
  optional<pos_info> const & get_break_at_pos() const override { return m_break_at_pos; }
  parser_pos_provider get_parser_pos_provider(pos_info const & some_pos) const override {
    return parser_pos_provider(rb_map<unsigned, pos_info, unsigned_cmp>(), m_file_name, some_pos, 0);
  }
  bool is_local_level(name const & n) const { return m_local_level_decls.contains(n); }
  bool is_local_level_variable(name const & n) const { return m_level_variables.contains(n); }
  void maybe_throw_error(parser_error && err) override;
  buffer<name> const & get_univ_params() const { return m_lp_params; }
  name get_name() const { return m_name; }
  buffer<expr> const & get_binders() { return m_params; }
  expr const & get_type() { return m_type; }
  const buffer<pair<buffer<expr>, expr>> & get_val() const { return m_val; }
  virtual expr save_pos(expr const & e, pos_info) override { return e; }
  virtual expr rec_save_pos(expr const & e, pos_info) override { return e; }
  virtual expr rec_save_pos(expr const & e, optional<pos_info>) override { return e; }
  virtual optional<pos_info> get_pos_info(expr const &) const override { return optional<pos_info>(m_pos); }
  optional<expr> get_well_founded_tac() const { return m_wf_tac; }

protected:
  virtual std::tuple<expr, expr, name> parse_definition(ast_data * parent, buffer<name> & lp_names, buffer<expr> & params,
                                                        bool is_example, bool is_instance, bool, bool) override;
};

void initialize_parser();
void finalize_parser();
}
