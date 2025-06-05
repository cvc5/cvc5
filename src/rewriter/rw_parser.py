###############################################################################
# Top contributors (to current version):
#   Haniel Barbosa, Leni Aniva, Andrew Reynolds
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Parser of the DSL rewrite rule compiler
##

import pyparsing as pp
from node import *
from rule import Rule
from util import die, fresh_name

symbol_to_op = {e.symbol: e for e in Op if e.symbol is not None}


class SymbolTable:
    def __init__(self):
        self.consts = {
            'real.pi': App(Op.REAL_PI, []),
            're.none': App(Op.REGEXP_NONE, []),
            're.all': App(Op.REGEXP_ALL, []),
            're.allchar': App(Op.REGEXP_ALLCHAR, []),
            '_': Placeholder(),
        }
        self.symbols = {}
        # Definitions must be decoupled from symbols because symbols have to be
        # bound as to not trigger an error from mkrewrites when it checks rule
        # validity.
        self.defs = {}

    def add_symbol(self, name, sort):
        if name in self.consts or name in self.symbols:
            die(f'Symbol {name} has already been declared')

        self.symbols[name] = Var(fresh_name(name), sort)
    def add_def(self, name, expr):
        if name in self.consts or name in self.symbols or name in self.defs:
            die(f'Definition {name} has already been declared')
        self.defs[name] = expr

    def get_symbol(self, name):
        if name in self.consts:
            return self.consts[name]

        if name not in self.symbols and name not in self.defs:
            die(f'Symbol {name} not declared')
        # Symbol collisions are checked, so symbol name shadowing is not
        # possible here.
        if name in self.defs:
            return self.defs[name]
        return self.symbols[name]

    def pop(self):
        # TODO: Actual push/pop
        self.symbols = {}
        self.defs = {}


class Parser:
    def __init__(self):
        self.symbols = SymbolTable()

    def get_symbols(self):
        return self.symbols

    def bv_to_int(self, s):
        assert s.startswith('bv')
        return int(s[2:])

    def symbol(self):
        special_chars = '=' + '_' + '+' + '-' + '<' + '>' + '*' + '.' + '@' + '/'
        return pp.Word(pp.alphas + special_chars, pp.alphanums + special_chars)

    def app_action(self, s, l, t):
        op = symbol_to_op[t[0]]
        if op == Op.SUB and len(t) == 2:
            op = Op.NEG
        return App(op, t[1:])
    
    # Action when parsing a decimal or numeral
    def number_parse_action(s, l, t):
        num_str = t[0]
        if '/' in num_str:
            return CRational(num_str)
        else:
            return CInt(int(num_str))

    def expr(self, allow_comprehension=True):
        expr = pp.Forward()

        # Variable
        var = self.symbol().setParseAction(
            lambda s, l, t: self.symbols.get_symbol(t[0]))

        # Constants
        bconst = pp.Keyword('true').setParseAction(
            lambda s, l, t: CBool(True)) | pp.Keyword('false').setParseAction(
                lambda s, l, t: CBool(False))
        # handles both rationals and numerals
        aconst = pp.Combine(
              pp.Word(pp.nums) + pp.Optional('/' + pp.Word(pp.nums))
          ).setParseAction(self.number_parse_action)
        strconst = pp.QuotedString(
            quoteChar='"').setParseAction(lambda s, l, t: CString(t[0]))

        # Function applications
        indexed_app = (pp.Suppress('(') + pp.Suppress('(') + pp.Suppress('_') +
                       self.symbol() + pp.OneOrMore(expr) + pp.Suppress(')') +
                       pp.OneOrMore(expr) + pp.Suppress(')')).setParseAction(
                           lambda s, l, t: App(symbol_to_op[t[0]], t[1:]))
        app = (pp.Suppress('(') + self.symbol() + pp.OneOrMore(expr) +
               pp.Suppress(')')).setParseAction(self.app_action)

        options = bconst | aconst | strconst | indexed_app | app | var
        if allow_comprehension:
            lambda_def = (pp.Suppress('(') + pp.Keyword('lambda') +
                          pp.Suppress('(') + self.symbol() + self.sort() +
                          pp.Suppress(')') + expr +
                          pp.Suppress(')')).setParseAction(lambda s, l, t: App(
                              Op.LAMBDA, [Var(t[1], t[2]), t[3]]))
            comprehension = (pp.Suppress('(') + pp.Keyword('map') +
                             lambda_def + expr() +
                             pp.Suppress(')')).setParseAction(
                                 lambda s, l, t: App(Op.MAP, [t[1], t[2]]))
            options = comprehension | options

        expr <<= options
        return expr

    def sort(self):
        bv_sort = (pp.Suppress('(') +
                   (pp.Suppress('_') + pp.Keyword('BitVec')) +
                   self.expr(False) + pp.Suppress(')')).setParseAction(
                       lambda s, l, t: Sort(BaseSort.BitVec, [t[1]]))
        int_sort = pp.Keyword('Int').setParseAction(
            lambda s, l, t: Sort(BaseSort.Int, []))
        real_sort = pp.Keyword('Real').setParseAction(
            lambda s, l, t: Sort(BaseSort.Real, []))
        bool_sort = pp.Keyword('Bool').setParseAction(
            lambda s, l, t: Sort(BaseSort.Bool, []))
        string_sort = pp.Keyword('String').setParseAction(
            lambda s, l, t: Sort(BaseSort.String, []))
        reglan_sort = pp.Keyword('RegLan').setParseAction(
            lambda s, l, t: Sort(BaseSort.RegLan, []))
        abs_array_sort = pp.Keyword('?Array').setParseAction(
            lambda s, l, t: Sort(BaseSort.AbsArray, []))
        abs_bv_sort = pp.Keyword('?BitVec').setParseAction(
            lambda s, l, t: Sort(BaseSort.AbsBitVec, []))
        abs_seq_sort = pp.Keyword('?Seq').setParseAction(
            lambda s, l, t: Sort(BaseSort.AbsSeq, []))
        abs_set_sort = pp.Keyword('?Set').setParseAction(
            lambda s, l, t: Sort(BaseSort.AbsSet, []))
        abs_abs_sort = pp.Keyword('?').setParseAction(
            lambda s, l, t: Sort(BaseSort.AbsAbs, []))
        return bv_sort | int_sort | real_sort | bool_sort | string_sort | \
            reglan_sort | abs_array_sort | abs_bv_sort | abs_seq_sort | \
            abs_set_sort | abs_abs_sort

    def var_decl_action(self, name, sort, attrs):
        if attrs:
            sort.is_list = True
        self.symbols.add_symbol(name, sort)
    def def_decl_action(self, name, expr):
        self.symbols.add_def(name, expr)

    def var_list(self):
        decl = pp.Suppress(
            (pp.Suppress('(') + self.symbol() + self.sort() +
             pp.Optional(pp.Keyword(':list')) +
             pp.Suppress(')')).setParseAction(
                 lambda s, l, t: self.var_decl_action(t[0], t[1], t[2:])))
        return (pp.Suppress('(') + pp.ZeroOrMore(decl) + pp.Suppress(')'))

    def def_list(self):
        d = pp.Suppress((pp.Suppress('(') + self.symbol() + self.expr()
                         + pp.Suppress(')'))
                .setParseAction(lambda s, l, t: self.def_decl_action(t[0], t[1])))
        return pp.Optional(pp.Suppress('(') + pp.Suppress(pp.Keyword('def')) +
                           pp.ZeroOrMore(d) + pp.Suppress(')'))

    def rule_action(self, name, cond, lhs, rhs, is_fixed_point, rhs_context):
        bvars = self.symbols.symbols.values()
        self.symbols.pop()
        return Rule(name, bvars, cond, lhs, rhs, is_fixed_point, rhs_context)

    def parse_rules(self, s):
        def rule_action(s, l, t):
            keys, args, match, target = t
            assert len(t) == 4
            return self.rule_action(args, CBool(True), match, target, False, None)
        rule = (
            pp.Suppress('(') +
            pp.Keyword('define-rule') +
            self.symbol() + self.var_list() + self.def_list() +
            self.expr() + self.expr() +
            pp.Suppress(')')).setParseAction(rule_action)
        def fixed_rule_action(s, l, t):
            # t = [key, args, match, target, (cond)]
            assert len(t) == 4 or len(t) == 5
            keys, args, match, target = t[:4]
            cond = Placeholder() if len(t) == 4 else t[4]
            return self.rule_action(args, CBool(True), match, target, True, cond)
        fixed_rule = (
            pp.Suppress('(') +
            pp.Keyword('define-rule*') +
            self.symbol() + self.var_list() + self.def_list() +
            self.expr() + self.expr() + pp.Optional(self.expr()) +
            pp.Suppress(')')).setParseAction(fixed_rule_action)
        def cond_rule_action(s, l, t):
            keys, args, cond, match, target = t
            return self.rule_action(args, cond, match, target, False, None)
        cond_rule = (
            pp.Suppress('(') +
            pp.Keyword('define-cond-rule') +
            self.symbol() + self.var_list() + self.def_list() +
            self.expr() + self.expr() + self.expr() +
            pp.Suppress(')')).setParseAction(cond_rule_action)
        rules = pp.OneOrMore(rule | fixed_rule | cond_rule) + pp.StringEnd()
        rules.ignore(';' + pp.restOfLine)
        return rules.parseString(s)
