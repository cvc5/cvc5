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
    '+': Op.PLUS,
    '-': Op.MINUS,
    'mod': Op.MOD,
    '*': Op.MULT,
    '<': Op.LT,
    '>': Op.GT,
    '>=': Op.GEQ,
    '<=': Op.LEQ,
    '=': Op.EQ,
    'ite': Op.ITE,
    'str.++': Op.STRING_CONCAT,
    'str.len': Op.STRING_LENGTH,
    'str.substr': Op.STRING_SUBSTR,
    'str.replace': Op.STRING_REPLACE,
}


class SymbolTable:
    def __init__(self):
        self.symbols = dict()

    def add_symbol(self, name, sort):
        if name in self.symbols:
            die(f'Symbol {name} has already been declared')

        self.symbols[name] = Var(fresh_name(name), sort)

    def get_symbol(self, name):
        if name not in self.symbols:
            die(f'Symbol {name} not declared')
        return self.symbols[name]

    def pop(self):
        # TODO: Actual push/pop
        self.symbols = dict()


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
               pp.Suppress(')')
               ).setParseAction(lambda s, l, t: App(symbol_to_op[t[0]], t[1:]))

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
        return bv_sort | int_sort | real_sort | bool_sort | string_sort

    def attrs(self):
        return pp.Keyword(':list') | pp.Keyword(':const')

    def var_list(self):
        decl = pp.Suppress(
            (pp.Suppress('(') + self.symbol() + self.sort() +
             pp.Suppress(')')).setParseAction(
                 lambda s, l, t: self.symbols.add_symbol(t[0], t[1])))
        return (pp.Suppress('(') + pp.ZeroOrMore(decl) + pp.Suppress(')'))

    def rule_action(self, name, cond, lhs, rhs):
        bvars = self.symbols.symbols.values()
        self.symbols.pop()
        return Rule(name, bvars, cond, lhs, rhs)

    def parse_rules(self, s):
        comments = pp.ZeroOrMore(pp.Suppress(pp.cStyleComment))

        rule = comments + (
            pp.Suppress('(') + pp.Keyword('define-rule') + self.symbol() +
            self.var_list() + self.expr() + self.expr() +
            pp.Suppress(')')).setParseAction(lambda s, l, t: self.rule_action(
                t[1], CBool(True), t[2], t[3]))
        cond_rule = comments + (
            pp.Suppress('(') + pp.Keyword('define-cond-rule') + self.symbol() +
            self.var_list() + self.expr() + self.expr() + self.expr() +
            pp.Suppress(')')).setParseAction(
                lambda s, l, t: self.rule_action(t[1], t[2], t[3], t[4]))
        rules = pp.OneOrMore(rule | cond_rule) + comments + pp.StringEnd()
        res = rules.parseString(s)
        return res
