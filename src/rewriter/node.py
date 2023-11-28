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
# Term data structures for different kinds of terms, sorts and values in the DSL
##

from enum import Enum, auto


class Op(Enum):

    ###########################################################################
    # Bit-vectors
    ###########################################################################

    # Bit-vector predicates
    BVUGT = auto()
    BVUGE = auto()
    BVSGT = auto()
    BVSGE = auto()
    BVSLT = auto()
    BVSLE = auto()
    BVULT = auto()
    BVULE = auto()
    BVREDAND = auto()
    BVREDOR = auto()

    # Bit-vector arithmetic
    BVNEG = auto()
    BVADD = auto()
    BVSUB = auto()
    BVMUL = auto()
    BVSDIV = auto()
    BVUDIV = auto()
    BVSREM = auto()
    BVUREM = auto()
    BVSMOD = auto()

    # Bit-vector shifts
    BVSHL = auto()
    BVLSHR = auto()
    BVASHR = auto()
    ROTATE_LEFT = auto()
    ROTATE_RIGHT = auto()

    # Bitwise bit-vector operations
    BVNOT = auto()
    BVAND = auto()
    BVOR = auto()
    BVXOR = auto()
    BVNAND = auto()
    BVNOR = auto()
    BVXNOR = auto()

    CONCAT = auto()

    BVITE = auto()
    BVCOMP = auto()

    BVCONST = auto()
    ZERO_EXTEND = auto()
    SIGN_EXTEND = auto()
    EXTRACT = auto()
    REPEAT = auto()

    ###########################################################################
    # Boolean
    ###########################################################################

    NOT = auto()
    AND = auto()
    OR = auto()
    IMPLIES = auto()
    XOR = auto()

    ###########################################################################
    # Arithmetic
    ###########################################################################

    NEG = auto()
    ADD = auto()
    SUB = auto()
    MULT = auto()
    INT_DIV = auto()
    DIV = auto()
    MOD = auto()
    ABS = auto()
    LT = auto()
    GT = auto()
    LEQ = auto()
    GEQ = auto()

    ###########################################################################
    # Theory-independent
    ###########################################################################

    EQ = auto()
    ITE = auto()
    LAMBDA = auto()
    BOUND_VARS = auto()

    ###########################################################################
    # Strings
    ###########################################################################

    CONST_STRING = auto()
    STRING_CONCAT = auto()
    STRING_IN_REGEXP = auto()
    STRING_LENGTH = auto()

    STRING_SUBSTR = auto()
    STRING_UPDATE = auto()
    STRING_AT = auto()
    STRING_CONTAINS = auto()
    STRING_LT = auto()
    STRING_LEQ = auto()
    STRING_INDEXOF = auto()
    STRING_INDEXOF_RE = auto()
    STRING_REPLACE = auto()
    STRING_REPLACE_ALL = auto()
    STRING_REPLACE_RE = auto()
    STRING_REPLACE_RE_ALL = auto()
    STRING_PREFIX = auto()
    STRING_SUFFIX = auto()
    STRING_IS_DIGIT = auto()
    STRING_ITOS = auto()
    STRING_STOI = auto()
    STRING_TO_CODE = auto()
    STRING_FROM_CODE = auto()
    STRING_TOLOWER = auto()
    STRING_TOUPPER = auto()
    STRING_REV = auto()

    STRING_TO_REGEXP = auto()
    REGEXP_CONCAT = auto()
    REGEXP_UNION = auto()
    REGEXP_INTER = auto()
    REGEXP_DIFF = auto()
    REGEXP_STAR = auto()
    REGEXP_PLUS = auto()
    REGEXP_OPT = auto()
    REGEXP_RANGE = auto()
    REGEXP_COMPLEMENT = auto()

    REGEXP_NONE = auto()
    REGEXP_ALLCHAR = auto()


class BaseSort(Enum):
    Bool = auto()
    BitVec = auto()
    Int = auto()
    Real = auto()
    String = auto()
    RegLan = auto()


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
        return self.base == other.base and self.is_list == other.is_list and super(
        ).__eq__(other)

    def __hash__(self):
        return hash((self.base, self.is_list, tupe(self.children)))

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
