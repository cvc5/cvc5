import pyparsing as pp
from node import *
from rule import Rule

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
    'xor': Op.XOR,
    '+': Op.PLUS,
    '-': Op.MINUS,
    'mod': Op.MOD,
    '*': Op.MULT,
    '<': Op.LT,
    '>=': Op.GEQ,
    '=': Op.EQ,
    'ite': Op.ITE,
    'str.++': Op.STRING_CONCAT,
}


class SymbolTable:
    def __init__(self):
        self.symbols = dict()

    def add_symbol(self, v, s):
        self.symbols[v] = s


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
        var = self.symbol().setParseAction(lambda s, l, t: Var(t[0]))

        # Constants
        bconst = pp.Keyword('true').setParseAction(
            lambda s, l, t: CBool(True)) | pp.Keyword('false').setParseAction(
                lambda s, l, t: CBool(False))
        iconst = pp.Word(
            pp.nums).setParseAction(lambda s, l, t: IntConst(int(t[0])))
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
            lambda s, l, t: Sort(BaseSort.Int32, []))
        bool_sort = pp.Keyword('Bool').setParseAction(
            lambda s, l, t: Sort(BaseSort.Bool, []))
        string_sort = pp.Keyword('String').setParseAction(
            lambda s, l, t: Sort(BaseSort.String, []))
        return bv_sort | int_sort | bool_sort | string_sort

    def attrs(self):
        return pp.Keyword(':list') | pp.Keyword(':const')

    def parse_rules(self, s):
        comments = pp.ZeroOrMore(pp.Suppress(pp.cStyleComment))

        decl = comments + pp.Suppress(
            (pp.Suppress('(') + pp.Keyword('declare-const') + self.symbol() +
             self.sort() + pp.Suppress(')')).setParseAction(
                 lambda s, l, t: self.symbols.add_symbol(t[1], t[2])))
        rule = comments + (pp.Suppress('(') + pp.Keyword('define-rule') +
                           pp.Word(pp.alphas) + self.expr() + self.expr() +
                           pp.Suppress(')')).setParseAction(
                               lambda s, l, t: Rule(t[1], t[2], t[3]))
        rules = pp.OneOrMore(decl | rule) + comments + pp.StringEnd()
        res = rules.parseString(s)
        return res
