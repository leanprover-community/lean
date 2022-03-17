/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Sebastian Ullrich
*/
#pragma once
#include <string>
#include <vector>
#include "util/name_map.h"
#include "util/exception_with_pos.h"
#include "util/task.h"
#include "kernel/pos_info_provider.h"

namespace lean {
/** \brief Exception used to track parsing erros, it does not leak outside of this class. */
struct parser_error : public exception_with_pos {
    pos_info m_pos;
    parser_error(char const * msg, pos_info const & p):exception_with_pos(msg), m_pos(p) {}
    parser_error(sstream const & msg, pos_info const & p):exception_with_pos(msg), m_pos(p) {}
    virtual optional<pos_info> get_pos() const override { return some(m_pos); }
    std::string const & get_msg() const { return m_msg; }
    virtual throwable * clone() const override { return new parser_error(m_msg.c_str(), m_pos); }
    virtual void rethrow() const override { throw *this; }
};

typedef unsigned ast_id;

struct ast_data {
    ast_id                  m_id;
    pos_info                m_start;
    optional<pos_info>      m_end;
    name                    m_type;
    std::vector<ast_id>     m_children;
    name                    m_value;
    optional<expr>          m_pexpr;
    optional<task<expr>>    m_expr;

    ast_data(ast_id id, pos_info start, name type, name value = {}):
        m_id(id), m_start(start), m_type(type), m_value(value) {}

    ast_data(ast_id id, pos_info start, pos_info end, name type, name value = {}):
        m_id(id), m_start(start), m_end(end), m_type(type), m_value(value) {}

    ast_data & push(ast_id id) {
        lean_assert(m_id != 0);
        m_children.push_back(id);
        return *this;
    }
};

/** \brief Base class for frontend parsers with basic functions */
class abstract_parser : public pos_info_provider {
public:
    /** \brief Return the current position information */
    virtual pos_info pos() const = 0;
    /** \brief Return true iff the current token is a keyword (or command keyword) named \c tk */
    virtual bool curr_is_token(name const & tk) const = 0;
    /** \brief Return true iff the current token is a numeral */
    virtual bool curr_is_numeral() const = 0;
    /** \brief Read the next token if the current one is not End-of-file. */
    virtual void next() = 0;

    virtual pair<ast_id, unsigned> parse_small_nat() = 0;
    virtual pair<ast_id, std::string> parse_string_lit() = 0;
};
}
