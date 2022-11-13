# -*- coding: utf-8 -*-
#
# Copyright (c) 2016 Microsoft Corporation. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Authors: Sebastian Ullrich, Gabriel Ebner
#

import gdb
import gdb.printing

class LeanOptionalPrinter:
    """Print a lean::optional object."""

    def __init__(self, val):
        self.val = val

    def get_val(self):
        if hasattr(self.val, 'm_some'):
            if not self.val['m_some']:
                return None
        elif not self.val['m_value'].cast(gdb.lookup_type('char').pointer()):
            return None
        return self.val['m_value']

    def children(self):
        val = self.get_val()
        return [('', val)] if val else []

    def to_string(self):
        return str(self.val.type)

class LeanNamePrinter:
    """Print a lean::name object."""

    def __init__(self, val):
        self.val = val

    def to_string(self):
        def rec(imp):
            s = ("'%s'" % imp['m_str'].string()) if imp['m_is_string'] else str(imp['m_k'])
            if imp['m_prefix']:
                return "%s.%s" % (rec(imp['m_prefix'].dereference()), s)
            else:
                return s

        if not self.val['m_ptr']:
            return ""
        else:
            return rec(self.val['m_ptr'].dereference())

class LeanSexprPrinter:
    expr_kinds = [
        (None, 'Nil', []),
        ('lean::sexpr_string', 'String', ['m_value']),
        ('lean::sexpr_bool', 'bool', ['m_value']),
        ('lean::sexpr_int', 'Int', ['m_value']),
        ('lean::sexpr_double', 'Double', ['m_value']),
        ('lean::sexpr_name', 'Name', ['m_value']),
        ('lean::sexpr_cons', 'Cons', ['m_head', 'm_tail']),
        ('lean::sexpr_ext', 'Ext', ['m_value']),
    ]

    def __init__(self, val):
        self.kind = int(val['m_ptr']['m_kind'] if val['m_ptr'] else 0)
        type_name = self.expr_kinds[self.kind][0]
        if type_name is not None:
            subtype = gdb.lookup_type(self.expr_kinds[self.kind][0])
            self.val = val['m_ptr'].cast(subtype.pointer()).dereference()
        else:
            self.val = None

    def to_string(self):
        return 'lean::sexpr[{}]'.format(self.expr_kinds[self.kind][1])

    def children(self):
        kind, _, fields = self.expr_kinds[self.kind]
        for f in fields:
            yield (f, self.val[f])
    # case sexpr_kind::Nil:         out << "nil"; break;
    # case sexpr_kind::String:      out << "\"" << escaped(to_string(s).c_str()) << "\""; break;
    # case sexpr_kind::Bool:        out << (to_bool(s) ? "true" : "false"); break;
    # case sexpr_kind::Int:         out << to_int(s); break;
    # case sexpr_kind::Double:      out << to_double(s); break;
    # case sexpr_kind::Name:        out << to_name(s); break;
    # case sexpr_kind::Ext:         to_ext(s).display(out); break;
    # case sexpr_kind::Cons: {
    #     out << "(";
    #     sexpr const * curr = &s;
    #     while (true) {
    #         out << head(*curr);
    #         curr = &tail(*curr);
    #         if (is_nil(*curr)) {
    #             break;
    #         } else if (!is_cons(*curr)) {
    #             out << " . ";
    #             out << *curr;
    #             break;
    #         } else {
    #             out << " ";
    #         }
    #     }
    #     out << ")";
    # }}
    # return out;

class LeanExprPrinter:
    """Print a lean::expr object."""

    expr_kinds = [
        ('lean::expr_var', 'Var', ['m_vidx']),
        ('lean::expr_sort', 'Sort', ['m_level']),
        ('lean::expr_const', 'Constant', ['m_name', 'm_levels']),
        ('lean::expr_mlocal', 'Meta', ['m_name', 'm_type']),
        ('lean::expr_local', 'Local', ['m_pp_name', 'm_name', 'm_bi', 'm_type']),
        ('lean::expr_app', 'App', ['m_fn', 'm_arg']),
        ('lean::expr_binding', 'Lambda', ['m_binder', 'm_body']),
        ('lean::expr_binding', 'Pi', ['m_binder', 'm_body']),
        ('lean::expr_let', 'Let', ['m_name', 'm_type', 'm_value', 'm_body']),
        ('lean::expr_macro', 'Macro', ['m_definition']),
    ]


    def __init__(self, val):
        self.kind = int(val['m_ptr']['m_kind'])
        subtype = gdb.lookup_type(LeanExprPrinter.expr_kinds[self.kind][0])
        self.val = val['m_ptr'].cast(subtype.pointer()).dereference()

    def to_string(self):
        return 'lean::expr[{}]'.format(LeanExprPrinter.expr_kinds[self.kind][1])

    def children(self):
        kind, _, fields = LeanExprPrinter.expr_kinds[self.kind]
        for f in fields:
            yield (f, self.val[f])
        if kind == 'lean::expr_macro':
            p = self.val.address.cast(gdb.lookup_type('char').pointer())
            p += gdb.lookup_type('lean::expr_macro').sizeof
            p = p.cast(gdb.lookup_type('lean::expr').pointer())
            for i in range(self.val['m_num_args']):
                yield ('[%s]' % i, (p + i).dereference())

class LeanLevelPrinter:
    """Print a lean::level object."""

    level_kinds = [
        ('lean::level_cell', 'zero', []),
        ('lean::level_succ', 'succ', ['m_l']),
        ('lean::level_max_core', 'max', ['m_lhs', 'm_rhs']),
        ('lean::level_max_core', 'imax', ['m_lhs', 'm_rhs']),
        ('lean::level_param_core', 'param', ['m_id']),
        ('lean::level_param_core', 'meta', ['m_id']),
    ]

    def __init__(self, val):
        self.val = val

    def to_string(self):
        kind = int(self.val['m_ptr']['m_kind'])
        (subtype, name, fields) = LeanLevelPrinter.level_kinds[kind]
        subtype = gdb.lookup_type(subtype)
        val = self.val['m_ptr'].cast(subtype.pointer()).dereference()
        return "({})".format(" ".join([name] + [str(val[field]) for field in fields]))

class LeanListPrinter:
    """Print a lean::list object."""

    def __init__(self, val):
        self.val = val

    def children(self):
        l = self.val
        i = 0
        while l['m_ptr']:
            cell = l['m_ptr'].dereference()
            yield ('[%s]' % i, cell['m_head'])
            l = cell['m_tail']
            i += 1

    def to_string(self):
        return str(self.val.type)

    def display_hint(self):
        return 'array'

class LeanBufferPrinter:
    """Print a lean::buffer object."""

    def __init__(self, val):
        self.val = val

    def children(self):
        p = self.val['m_buffer']
        for i in range(int(self.val['m_pos'])):
            yield ('[%s]' % i, p.dereference())
            p += 1

    def to_string(self):
        return str(self.val.type)

    def display_hint(self):
        return 'array'

class LeanRBTreePrinter:
    """Print a lean::rb_tree object."""

    def __init__(self, val):
        self.val = val

    def children(self):
        def rec(node):
            if node['m_ptr']:
                cell = node['m_ptr'].dereference()
                for i in rec(cell['m_left']): yield i
                yield ('', cell['m_value'])
                for i in rec(cell['m_right']): yield i
        return rec(self.val['m_root'])

    def to_string(self):
        return 'lean::rb_tree' # full type is way too verbose

    def display_hint(self):
        return 'array'

class LeanRBMapPrinter:
    """Print a lean::rb_map object."""

    def __init__(self, val):
        self.val = val

    def children(self):
        for (_, child) in LeanRBTreePrinter(self.val['m_map']).children():
            yield ('', child['first'])
            yield ('', child['second'])

    def to_string(self):
        return 'lean::rb_map' # full type is way too verbose

    def display_hint(self):
        return 'map'

def build_pretty_printer():
    pp = gdb.printing.RegexpCollectionPrettyPrinter("lean")
    pp.add_printer('optional', '^lean::optional', LeanOptionalPrinter)
    pp.add_printer('name', '^lean::name$', LeanNamePrinter)
    pp.add_printer('expr', '^lean::expr$', LeanExprPrinter)
    pp.add_printer('level', '^lean::level$', LeanLevelPrinter)
    pp.add_printer('list', '^lean::list', LeanListPrinter)
    pp.add_printer('buffer', '^lean::buffer', LeanBufferPrinter)
    pp.add_printer('rb_tree', '^lean::rb_tree', LeanRBTreePrinter)
    pp.add_printer('rb_map', '^lean::rb_map', LeanRBMapPrinter)
    return pp

def register():
    gdb.printing.register_pretty_printer(
        gdb.current_objfile(),
        build_pretty_printer(),
        replace=True)

register()
