###############################################################################
# Top contributors (to current version):
#   Leni Aniva, Haniel Barbosa, Andrew Reynolds
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Term data structures for different kinds of terms, sorts and values in the DSL
##

from enum import Enum, auto


class Op(Enum):

    def __new__(cls, symbol, kind):
        """
        symbol: The name of the operator in RARE
        kind: The name of the operator in CVC5
        """
        entry = object.__new__(cls)
        entry._value_ = kind
        entry.symbol = symbol
        entry.kind = kind
        return entry

    ###########################################################################
    # Arrays
    ###########################################################################
    STORE = ('store', 'STORE')
    SELECT = ('select', 'SELECT')

    ###########################################################################
    # Bit-vectors
    ###########################################################################

    # Bit-vector predicates
    BVUGT = ('bvugt', 'BITVECTOR_UGT')
    BVUGE = ('bvuge', 'BITVECTOR_UGE')
    BVSGT = ('bvsgt', 'BITVECTOR_SGT')
    BVSGE = ('bvsge', 'BITVECTOR_SGE')
    BVSLT = ('bvslt', 'BITVECTOR_SLT')
    BVSLE = ('bvsle', 'BITVECTOR_SLE')
    BVULT = ('bvult', 'BITVECTOR_ULT')
    BVULE = ('bvule', 'BITVECTOR_ULE')
    BVREDAND = ('bvredand', 'BITVECTOR_REDAND')
    BVREDOR = ('bvredor', 'BITVECTOR_REDOR')

    # Bit-vector arithmetic
    BVNEG = ('bvneg', 'BITVECTOR_NEG')
    BVADD = ('bvadd', 'BITVECTOR_ADD')
    BVSUB = ('bvsub', 'BITVECTOR_SUB')
    BVMUL = ('bvmul', 'BITVECTOR_MULT')
    BVSDIV = ('bvsdiv', 'BITVECTOR_SDIV')
    BVUDIV = ('bvudiv', 'BITVECTOR_UDIV')
    BVSREM = ('bvsrem', 'BITVECTOR_SREM')
    BVUREM = ('bvurem', 'BITVECTOR_UREM')
    BVSMOD = ('bvsmod', 'BITVECTOR_SMOD')

    # Bit-vector shifts
    BVSHL = ('bvshl', 'BITVECTOR_SHL')
    BVLSHR = ('bvlshr', 'BITVECTOR_LSHR')
    BVASHR = ('bvashr', 'BITVECTOR_ASHR')
    ROTATE_LEFT = ('rotate_left', 'BITVECTOR_ROTATE_LEFT')
    ROTATE_RIGHT = ('rotate_right', 'BITVECTOR_ROTATE_RIGHT')

    # Bitwise bit-vector operations
    BVNOT = ('bvnot', 'BITVECTOR_NOT')
    BVAND = ('bvand', 'BITVECTOR_AND')
    BVOR = ('bvor', 'BITVECTOR_OR')
    BVXOR = ('bvxor', 'BITVECTOR_XOR')
    BVNAND = ('bvnand', 'BITVECTOR_NAND')
    BVNOR = ('bvnor', 'BITVECTOR_NOR')
    BVXNOR = ('bvxnor', 'BITVECTOR_XNOR')
    BVUADDO = ('bvuaddo', 'BITVECTOR_UADDO')
    BVSADDO = ('bvsaddo', 'BITVECTOR_SADDO')
    BVUMULO = ('bvumulo', 'BITVECTOR_UMULO')
    BVSMULO = ('bvsmulo', 'BITVECTOR_SMULO')
    BVUSUBO = ('bvusubo', 'BITVECTOR_USUBO')
    BVSSUBO = ('bvssubo', 'BITVECTOR_SSUBO')
    BVSDIVO = ('bvsdivo', 'BITVECTOR_SDIVO')
    BVNEGO = ('bvnego', 'BITVECTOR_NEGO')

    BVITE = ('bvite', 'BITVECTOR_ITE')
    BVCOMP = ('bvcomp', 'BITVECTOR_COMP')

    ZERO_EXTEND = ('zero_extend', 'BITVECTOR_ZERO_EXTEND')
    SIGN_EXTEND = ('sign_extend', 'BITVECTOR_SIGN_EXTEND')
    CONCAT = ('concat', 'BITVECTOR_CONCAT')
    EXTRACT = ('extract', 'BITVECTOR_EXTRACT')
    REPEAT = ('repeat', 'BITVECTOR_REPEAT')

    BVSIZE = ('@bvsize', 'BITVECTOR_SIZE')
    BVCONST = ('@bv', 'CONST_BITVECTOR_SYMBOLIC')

    ###########################################################################
    # Boolean
    ###########################################################################

    NOT = ('not', 'NOT')
    AND = ('and', 'AND')
    OR = ('or', 'OR')
    IMPLIES = ('=>', 'IMPLIES')
    XOR = ('xor', 'XOR')

    ###########################################################################
    # Arithmetic
    ###########################################################################

    NEG = (None, 'NEG')  # This is parsed with SUB, so the key is None
    ADD = ('+', 'ADD')
    SUB = ('-', 'SUB')
    MULT = ('*', 'MULT')
    INT_DIV = ('div', 'INTS_DIVISION')
    INT_DIV_TOTAL = ('div_total', 'INTS_DIVISION_TOTAL')
    DIV = ('/', 'DIVISION')
    DIV_TOTAL = ('/_total', 'DIVISION_TOTAL')
    MOD = ('mod', 'INTS_MODULUS')
    MOD_TOTAL = ('mod_total', 'INTS_MODULUS_TOTAL')
    ABS = ('abs', 'ABS')
    LT = ('<', 'LT')
    GT = ('>', 'GT')
    LEQ = ('<=', 'LEQ')
    GEQ = ('>=', 'GEQ')
    POW2 = ('int.pow2', 'POW2')
    TO_INT = ('to_int', 'TO_INTEGER')
    TO_REAL = ('to_real', 'TO_REAL')
    IS_INT = ('is_int', 'IS_INTEGER')
    DIVISIBLE = ('divisible', 'DIVISIBLE')
    
    SINE = ('sin', 'SINE')
    COSINE = ('cos', 'COSINE')
    TANGENT = ('tan', 'TANGENT')
    SECANT = ('sec', 'SECANT')
    COSECANT = ('csc', 'COSECANT')
    COTANGENT = ('cot', 'COTANGENT')
    REAL_PI = (None, 'PI')  # Handled as constant

    INT_ISPOW2 = ('int.ispow2', 'INTS_ISPOW2')  # Backdoor for some bv rewrites
    INT_LENGTH = ('int.log2', 'INTS_LOG2')  # Backdoor for some bv rewrites

    ###########################################################################
    # Theory-independent
    ###########################################################################

    EQ = ('=', 'EQUAL')
    ITE = ('ite', 'ITE')
    # Lambda is not an operator. It exists here as a backdoor to simplify
    # parsing logic.
    LAMBDA = (None, 'LAMBDA')
    BOUND_VARS = (None, 'BOUND_VAR_LIST')
    DISTINCT = ('distinct', 'DISTINCT')

    UBV_TO_INT = ('ubv_to_int', 'BITVECTOR_UBV_TO_INT')
    SBV_TO_INT = ('sbv_to_int', 'BITVECTOR_SBV_TO_INT')
    INT_TO_BV = ('int_to_bv', 'INT_TO_BITVECTOR')
    
    TYPE_OF = ('@type_of', 'TYPE_OF')

    ###########################################################################
    # Strings
    ###########################################################################

    STRING_CONCAT = ('str.++', 'STRING_CONCAT')
    STRING_IN_REGEXP = ('str.in_re', 'STRING_IN_REGEXP')
    STRING_LENGTH = ('str.len', 'STRING_LENGTH')

    STRING_SUBSTR = ('str.substr', 'STRING_SUBSTR')
    STRING_UPDATE = ('str.update', 'STRING_UPDATE')
    STRING_AT = ('str.at', 'STRING_CHARAT')
    STRING_CONTAINS = ('str.contains', 'STRING_CONTAINS')
    STRING_LT = ('str.<', 'STRING_LT')
    STRING_LEQ = ('str.<=', 'STRING_LEQ')
    STRING_INDEXOF = ('str.indexof', 'STRING_INDEXOF')
    STRING_INDEXOF_RE = ('str.indexof_re', 'STRING_INDEXOF_RE')
    STRING_REPLACE = ('str.replace', 'STRING_REPLACE')
    STRING_REPLACE_ALL = ('str.replace_all', 'STRING_REPLACE_ALL')
    STRING_REPLACE_RE = ('str.replace_re', 'STRING_REPLACE_RE')
    STRING_REPLACE_RE_ALL = ('str.replace_re_all', 'STRING_REPLACE_RE_ALL')
    STRING_PREFIX = ('str.prefixof', 'STRING_PREFIX')
    STRING_SUFFIX = ('str.suffixof', 'STRING_SUFFIX')
    STRING_IS_DIGIT = ('str.is_digit', 'STRING_IS_DIGIT')
    STRING_ITOS = ('str.from_int', 'STRING_ITOS')
    STRING_STOI = ('str.to_int', 'STRING_STOI')
    STRING_TO_CODE = ('str.to_code', 'STRING_TO_CODE')
    STRING_FROM_CODE = ('str.from_code', 'STRING_FROM_CODE')
    STRING_TO_LOWER = ('str.to_lower', 'STRING_TO_LOWER')
    STRING_TO_UPPER = ('str.to_upper', 'STRING_TO_UPPER')
    STRING_REV = ('str.rev', 'STRING_REV')

    SEQ_UNIT = ('seq.unit', 'SEQ_UNIT')
    SEQ_NTH = ('seq.nth', 'SEQ_NTH')
    SEQ_EMPTY_OF_TYPE = ('@seq.empty_of_type', 'SEQ_EMPTY_OF_TYPE')

    STRING_TO_REGEXP = ('str.to_re', 'STRING_TO_REGEXP')
    REGEXP_CONCAT = ('re.++', 'REGEXP_CONCAT')
    REGEXP_UNION = ('re.union', 'REGEXP_UNION')
    REGEXP_INTER = ('re.inter', 'REGEXP_INTER')
    REGEXP_DIFF = ('re.diff', 'REGEXP_DIFF')
    REGEXP_STAR = ('re.*', 'REGEXP_STAR')
    REGEXP_PLUS = ('re.+', 'REGEXP_PLUS')
    REGEXP_REPEAT = ('re.^', 'REGEXP_REPEAT')
    REGEXP_OPT = ('re.opt', 'REGEXP_OPT')
    REGEXP_RANGE = ('re.range', 'REGEXP_RANGE')
    REGEXP_COMPLEMENT = ('re.comp', 'REGEXP_COMPLEMENT')
    REGEXP_LOOP = ('re.loop', 'REGEXP_LOOP')

    REGEXP_NONE = (None, 'REGEXP_NONE')  # Handled as constants
    REGEXP_ALL = (None, 'REGEXP_ALL')
    REGEXP_ALLCHAR = (None, 'REGEXP_ALLCHAR')

    ###########################################################################
    # Sets
    ###########################################################################

    SET_INTER = ('set.inter', 'SET_INTER')
    SET_UNION = ('set.union', 'SET_UNION')
    SET_MINUS = ('set.minus', 'SET_MINUS')
    SET_SUBSET = ('set.subset', 'SET_SUBSET')
    SET_MEMBER = ('set.member', 'SET_MEMBER')
    SET_SINGLETON = ('set.singleton', 'SET_SINGLETON')
    SET_CHOOSE = ('set.choose', 'SET_CHOOSE')
    SET_CARD = ('set.card', 'SET_CARD')
    SET_IS_EMPTY = ('set.is_empty', 'SET_IS_EMPTY')
    SET_IS_SINGLETON = ('set.is_singleton', 'SET_IS_SINGLETON')
    SET_EMPTY_OF_TYPE = ('@set.empty_of_type', 'SET_EMPTY_OF_TYPE')


class BaseSort(Enum):
    Bool = auto()
    BitVec = auto()
    Int = auto()
    Real = auto()
    String = auto()
    RegLan = auto()
    AbsArray = auto()
    AbsBitVec = auto()
    AbsSeq = auto()
    AbsSet = auto()
    AbsAbs = auto()


class Node:
    def __init__(self, children, sort=None):
        assert all(isinstance(child, Node) for child in children)
        self.children = children
        self.sort = sort
        self.name = None

    def __getitem__(self, i):
        return self.children[i]

    def __eq__(self, other):
        if len(self.children) != len(other.children):
            return False

        for c1, c2 in zip(self.children, other.children):
            if c1 != c2:
                return False

        return True


class Sort(Node):
    def __init__(self, base, args=None, is_list=False, is_const=False):
        super().__init__(args if args else [])
        self.base = base
        self.is_list = is_list
        self.is_const = is_const

    def __eq__(self, other):
        return self.base == other.base and self.is_list == other.is_list and\
            super().__eq__(other)

    def __hash__(self):
        return hash((self.base, self.is_list, tuple(self.children)))

    def __repr__(self):
        rep = ''
        if len(self.children) == 0:
            rep = '{}'.format(self.base)
        else:
            rep = '({} {})'.format(
                self.base, ' '.join(str(child) for child in self.children))
        if self.is_list:
            rep = rep + ' :list'
        return rep

    def is_int(self):
        return self.base == BaseSort.Int


class Placeholder(Node):
    def __init__(self):
        super().__init__([], None)

    def __eq__(self, other):
        return isinstance(other, Placeholder)

    def __hash__(self):
        return hash('_')

    def __repr__(self):
        return '_'


class Var(Node):
    def __init__(self, name, sort=None):
        super().__init__([], sort)
        self.name = name

    def __eq__(self, other):
        return self.name == other.name

    def __hash__(self):
        return hash(self.name)

    def __repr__(self):
        return self.name


class CBool(Node):
    def __init__(self, val):
        super().__init__([])
        self.val = val

    def __eq__(self, other):
        assert isinstance(other, Node)
        return isinstance(other, CBool) and self.val == other.val

    def __hash__(self):
        return hash(self.val)

    def __repr__(self):
        return str(self.val)


class CInt(Node):
    def __init__(self, val):
        super().__init__([])
        self.val = val

    def __eq__(self, other):
        return isinstance(other, CInt) and self.val == other.val

    def __hash__(self):
        return hash(self.val)

    def __repr__(self):
        return str(self.val)

class CRational(Node):
    def __init__(self, val):
        super().__init__([])
        self.val = val

    def __eq__(self, other):
        return isinstance(other, CRational) and self.val == other.val

    def __hash__(self):
        return hash(self.val)

    def __repr__(self):
        return str(self.val)

class CString(Node):
    def __init__(self, val):
        super().__init__([])
        self.val = val

    def __eq__(self, other):
        return self.val == other.val

    def __hash__(self):
        return hash(self.val)

    def __repr__(self):
        return f'"{self.val}"'


class App(Node):
    def __init__(self, op, args):
        super().__init__(args)
        self.op = op

    def __eq__(self, other):
        return isinstance(
            other, App) and self.op == other.op and super().__eq__(other)

    def __hash__(self):
        return hash((self.op, tuple(self.children)))

    def __repr__(self):
        return '({} {})'.format(
            self.op, ' '.join(str(child) for child in self.children))
