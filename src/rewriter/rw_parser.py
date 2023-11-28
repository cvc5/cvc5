###############################################################################
# Top contributors (to current version):
#   Haniel Barbosa
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

symbol_to_op = {
    'bvugt': Op.BVUGT,
    'bvuge': Op.BVUGE,
    'bvsgt': Op.BVSGT,
    'bvsge': Op.BVSGE,
    'bvslt': Op.BVSLT,
    'bvsle': Op.BVSLE,
    'bvult': Op.BVULT,
    'bvule': Op.BVULE,
    'bvredand': Op.BVREDAND,
    'bvredor': Op.BVREDOR,
    'bvneg': Op.BVNEG,
    'bvadd': Op.BVADD,
    'bvsub': Op.BVSUB,
    'bvmul': Op.BVMUL,
    'bvsdiv': Op.BVSDIV,
    'bvudiv': Op.BVUDIV,
    'bvsrem': Op.BVSREM,
    'bvurem': Op.BVUREM,
    'bvsmod': Op.BVSMOD,
    'bvshl': Op.BVSHL,
    'bvlshr': Op.BVLSHR,
    'bvashr': Op.BVASHR,
    'rotate_left': Op.ROTATE_LEFT,
    'rotate_right': Op.ROTATE_RIGHT,
    'bvnot': Op.BVNOT,
    'bvand': Op.BVAND,
    'bvor': Op.BVOR,
    'bvxor': Op.BVXOR,
    'bvnand': Op.BVNAND,
    'bvnor': Op.BVNOR,
    'bvxnor': Op.BVXNOR,
    'concat': Op.CONCAT,
    'bvite': Op.BVITE,
    'bvcomp': Op.BVCOMP,
    'bv': Op.BVCONST,
    'zero_extend': Op.ZERO_EXTEND,
    'sign_extend': Op.SIGN_EXTEND,
    'extract': Op.EXTRACT,
    'repeat': Op.REPEAT,
    'not': Op.NOT,
    'and': Op.AND,
    'or': Op.OR,
    '=>': Op.IMPLIES,
    'xor': Op.XOR,
    '+': Op.ADD,
    '-': Op.SUB,
    '*': Op.MULT,
    'div': Op.INT_DIV,
    '/': Op.DIV,
    'mod': Op.MOD,
    'abs': Op.ABS,
    '<': Op.LT,
    '>': Op.GT,
    '<=': Op.LEQ,
    '>=': Op.GEQ,
    '=': Op.EQ,
    'ite': Op.ITE,
    'str.++': Op.STRING_CONCAT,
    'str.in_re': Op.STRING_IN_REGEXP,
    'str.len': Op.STRING_LENGTH,
    'str.substr': Op.STRING_SUBSTR,
    'str.update': Op.STRING_UPDATE,
    'str.at': Op.STRING_AT,
    'str.contains': Op.STRING_CONTAINS,
    'str.<': Op.STRING_LT,
    'str.<=': Op.STRING_LEQ,
    'str.indexof': Op.STRING_INDEXOF,
    'str.indexof_re': Op.STRING_INDEXOF_RE,
    'str.replace': Op.STRING_REPLACE,
    'str.replace_all': Op.STRING_REPLACE_ALL,
    'str.replace_re': Op.STRING_REPLACE_RE,
    'str.replace_re_all': Op.STRING_REPLACE_RE_ALL,
    'str.prefixof': Op.STRING_PREFIX,
    'str.suffixof': Op.STRING_SUFFIX,
    'str.is_digit': Op.STRING_IS_DIGIT,
    'str.from_int': Op.STRING_ITOS,
    'str.to_int': Op.STRING_STOI,
    'str.to_code': Op.STRING_TO_CODE,
    'str.from_code': Op.STRING_FROM_CODE,
    'str.tolower': Op.STRING_TOLOWER,
    'str.toupper': Op.STRING_TOUPPER,
    'str.rev': Op.STRING_REV,
    'str.to_re': Op.STRING_TO_REGEXP,
    're.++': Op.REGEXP_CONCAT,
    're.union': Op.REGEXP_UNION,
    're.inter': Op.REGEXP_INTER,
    're.diff': Op.REGEXP_DIFF,
    're.*': Op.REGEXP_STAR,
    're.+': Op.REGEXP_PLUS,
    're.opt': Op.REGEXP_OPT,
    're.range': Op.REGEXP_RANGE,
    're.comp': Op.REGEXP_COMPLEMENT,
}


class SymbolTable:
    def __init__(self):
        self.consts = {
            're.none': App(Op.REGEXP_NONE, []),
            're.allchar': App(Op.REGEXP_ALLCHAR, []),
            '_': Placeholder(),
        }
        self.symbols = {}

    def add_symbol(self, name, sort):
        if name in self.consts or name in self.symbols:
            die(f'Symbol {name} has already been declared')

        self.symbols[name] = Var(fresh_name(name), sort)

    def get_symbol(self, name):
        if name in self.consts:
            return self.consts[name]

        if name not in self.symbols:
            die(f'Symbol {name} not declared')
        return self.symbols[name]

    def pop(self):
        # TODO: Actual push/pop
        self.symbols = {}


class Parser:
    def __init__(self):
        self.symbols = SymbolTable()

    def get_symbols(self):
        return self.symbols

    def bv_to_int(self, s):
        assert s.startswith('bv')
        return int(s[2:])

    def symbol(self):
        special_chars = '=' + '_' + '+' + '-' + '<' + '>' + '*' + '.'
        return pp.Word(pp.alphas + special_chars, pp.alphanums + special_chars)

    def mk_let(self, let):
        body = let[-1]
        for binding in reversed(let[0:-1]):
            body = App(Op.LET, [binding[0], binding[1], body])
        return body

    def mk_case(self, cases):
        if not isinstance(cases[-1], Fn) or cases[-1].op != Op.CASE:
            cases[-1] = App(Op.CASE, [CBool(True), cases[-1]])
        else:
            cases.append(App(Op.CASE, [CBool(True), App(Op.FAIL, [])]))
        return App(Op.COND, cases)

    def app_action(self, s, l, t):
        op = symbol_to_op[t[0]]
        if op == Op.SUB and len(t) == 2:
            op = Op.NEG
        return App(op, t[1:])

    def expr(self, allow_comprehension=True):
        expr = pp.Forward()

        # Variable
        var = self.symbol().setParseAction(
            lambda s, l, t: self.symbols.get_symbol(t[0]))

        # Constants
        bconst = pp.Keyword('true').setParseAction(
            lambda s, l, t: CBool(True)) | pp.Keyword('false').setParseAction(
                lambda s, l, t: CBool(False))
        iconst = pp.Word(
            pp.nums).setParseAction(lambda s, l, t: CInt(int(t[0])))
        bvconst = (
            pp.Suppress('(') + pp.Suppress('_') + pp.Keyword('bv') + expr +
            expr +
            ')').setParseAction(lambda s, l, t: App(Op.BVCONST, [t[1], t[2]]))
        strconst = pp.QuotedString(
            quoteChar='"').setParseAction(lambda s, l, t: CString(t[0]))

        # Function applications
        indexed_app = (pp.Suppress('(') + pp.Suppress('(') + pp.Suppress('_') +
                       self.symbol() + pp.OneOrMore(expr) + pp.Suppress(')') +
                       pp.OneOrMore(expr) + pp.Suppress(')')).setParseAction(
                           lambda s, l, t: App(symbol_to_op[t[0]], t[1:]))
        app = (pp.Suppress('(') + self.symbol() + pp.OneOrMore(expr) +
               pp.Suppress(')')).setParseAction(self.app_action)

        # Let bindings
        binding = (
            pp.Suppress('(') + var + expr +
            pp.Suppress(')')).setParseAction(lambda s, l, t: (t[0], t[1]))
        let = (pp.Suppress('(') + pp.Keyword('let') + pp.Suppress('(') +
               pp.OneOrMore(binding) + pp.Suppress(')') + expr +
               pp.Suppress(')')).setParseAction(lambda s, l, t: mk_let(t[1:]))

        # Conditionals
        case = (pp.Suppress('(') + expr + expr + pp.Suppress(')')
                ).setParseAction(lambda s, l, t: App(Op.CASE, [t[0], t[1]]))
        cond = (
            pp.Suppress('(') + pp.Keyword('cond') + pp.OneOrMore(case) +
            pp.Optional(expr) +
            pp.Suppress(')')).setParseAction(lambda s, l, t: mk_case(t[1:]))

        options = bconst | iconst | bvconst | strconst | cond | indexed_app | app | let | var
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
        return bv_sort | int_sort | real_sort | bool_sort | string_sort | reglan_sort

    def var_decl_action(self, name, sort, attrs):
        if attrs:
            sort.is_list = True
        self.symbols.add_symbol(name, sort)

    def var_list(self):
        decl = pp.Suppress(
            (pp.Suppress('(') + self.symbol() + self.sort() +
             pp.Optional(pp.Keyword(':list')) +
             pp.Suppress(')')).setParseAction(
                 lambda s, l, t: self.var_decl_action(t[0], t[1], t[2:])))
        return (pp.Suppress('(') + pp.ZeroOrMore(decl) + pp.Suppress(')'))

    def rule_action(self, name, cond, lhs, rhs, is_fixed_point, rhs_context):
        bvars = self.symbols.symbols.values()
        self.symbols.pop()
        return Rule(name, bvars, cond, lhs, rhs, is_fixed_point, rhs_context)

    def parse_rules(self, s):
        rule = (
            pp.Suppress('(') +
            (pp.Keyword('define-rule*') | pp.Keyword('define-rule')) +
            self.symbol() + self.var_list() + self.expr() + self.expr() + pp.Optional(self.expr()) +
            pp.Suppress(')')).setParseAction(lambda s, l, t: self.rule_action(
                t[1], CBool(True), t[2], t[3], t[0] == 'define-rule*', t[4] if len(t) == 5 else None))
        cond_rule = (
            pp.Suppress('(') +
            (pp.Keyword('define-cond-rule*') | pp.Keyword('define-cond-rule'))
            + self.symbol() + self.var_list() + self.expr() + self.expr() +
            self.expr() + pp.Optional(self.expr()) +
            pp.Suppress(')')).setParseAction(lambda s, l, t: self.rule_action(
                t[1], t[2], t[3], t[4], t[0] == 'define-cond-rule*', t[5] if len(t) == 6 else None))
        rules = pp.OneOrMore(rule | cond_rule) + pp.StringEnd()
        rules.ignore(';' + pp.restOfLine)
        return rules.parseString(s)
