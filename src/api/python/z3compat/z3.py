############################################
# Copyright (c) 2021 The cvc5 Developers
#               2012 The Microsoft Corporation
#
# cvc5's Z3-based Python interface
#
# Author: Alex Ozdemir (aozdemir)
# pyz3 Author: Leonardo de Moura (leonardo)
############################################

"""
cvc5 is an SMT solver.

This is its (as much as possible) Z3-compatible python interface.

Several online tutorials for Z3Py are available at:
http://rise4fun.com/Z3Py/tutorial/guide

Please send feedback, comments and/or corrections on the Issue tracker for
https://github.com/cvc5/cvc5.git. Your comments are very valuable.

Small example: TODO
"""
from .z3printer import *
from fractions import Fraction
from decimal import Decimal
import decimal
import sys
import io
import math
import copy
import functools as ft
import operator as op

import pycvc5 as pc
from pycvc5 import kinds

DEBUG = __debug__


def debugging():
    global DEBUG
    return DEBUG


def _is_int(v):
    """ Python 2/3 agnostic int testing """
    if sys.version < "3":
        return isinstance(v, (int, long))
    else:
        return isinstance(v, int)


def unimplemented(msg=None):
    if msg is None:
        raise Exception("Unimplemented")
    else:
        raise Exception("Unimplemented: {}".format(msg))


class Z3Exception(Exception):
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return str(self.value)


# We use _assert instead of the assert command because we want to
# produce nice error messages in Z3Py at rise4fun.com
def _assert(cond, msg):
    if not cond:
        raise Z3Exception(msg)


# Hack for having nary functions that can receive one argument that is the
# list of arguments.
# Use this when function takes a single list of arguments
def _get_args(args):
    try:
        if len(args) == 1 and (isinstance(args[0], tuple) or isinstance(args[0], list)):
            return list(args[0])
        else:
            return list(args)
    except:  # len is not necessarily defined when args is not a sequence (use reflection?)
        return list(args)


# Use this when function takes multiple arguments
def _get_args_ast_list(args):
    try:
        if isinstance(args, set) or isinstance(args, tuple):
            return [arg for arg in args]
        else:
            return args
    except:
        return args


def _to_param_value(val):
    if isinstance(val, bool):
        if val:
            return "true"
        else:
            return "false"
    else:
        return str(val)


class Context(object):
    """A Context manages all terms, configurations, etc.

    In cvc5's API, these are managed by a solver, but we keep the Context class
    (which just wraps a solver) for compatiblity.

    It's only responsibilities are:
        * making fresh identifiers for a given sort
        * looking up previously defined constants
    """

    def __init__(self, *args, **kws):
        self.solver = pc.Solver()
        self.solver.setOption("produce-models", "true")
        # Map from (name, sort) pairs to constant terms
        self.vars = {}
        # An increasing identifier used to make fresh identifiers
        self.next_fresh_var = 0

    def __del__(self):
        self.solver = None

    def get_var(self, name, sort):
        """Get the variable identified by `name`.

        If no variable of that name (with that sort) has been created, creates
        one.

        Returns a Term
        """
        if (name, sort) not in self.vars:
            self.vars[(name, sort)] = self.solver.mkConst(sort.ast, name)
        return self.vars[(name, sort)]

    def next_fresh(self, sort, prefix):
        """Make a name such that (name, sort) is fresh.

        The name will be prefixed by `prefix`"""
        name = "{}{}".format(prefix, self.next_fresh_var)
        while (name, sort) in self.vars:
            self.next_fresh_var += 1
            name = "{}{}".format(prefix, self.next_fresh_var)
        return name

    def __eq__(self, o):
        return self.solver is o.solver


# Global Z3 context
_main_ctx = None


def main_ctx():
    """Return a reference to the global context.

    >>> x = Real('x')
    >>> x.ctx == main_ctx()
    True
    >>> c = Context()
    >>> c == main_ctx()
    False
    >>> x2 = Real('x', c)
    >>> x2.ctx == c
    True
    >>> eq(x, x2)
    False
    """
    global _main_ctx
    if _main_ctx is None:
        _main_ctx = Context()
    return _main_ctx


def _get_ctx(ctx):
    return main_ctx() if ctx is None else ctx


#########################################
#
# Term base class
#
#########################################


class ExprRef(object):
    """Constraints, formulas and terms are expressions."""

    def __init__(self, ast, ctx=None, reverse_children=False):
        self.ast = ast
        self.ctx = _get_ctx(ctx)
        self.reverse_children = reverse_children
        assert isinstance(self.ast, pc.Term)
        assert isinstance(self.ctx, Context)

    def __del__(self):
        if self.ctx is not None and self.ast is not None:
            self.ctx = None
            self.ast = None


#########################################
#
# Sorts
#
#########################################


class SortRef(object):
    """A Sort is essentially a type. Every term has a sort"""

    def __init__(self, ast, ctx=None):
        self.ast = ast
        self.ctx = _get_ctx(ctx)
        assert isinstance(self.ast, pc.Sort)
        assert isinstance(self.ctx, Context)

    def __del__(self):
        if self.ctx is not None:
            self.ctx = None
        if self.ast is not None:
            self.ast = None


class Solver(object):
    """Solver API provides methods for implementing the main SMT 2.0 commands:
    * push,
    * pop,
    * check,
    * get-model,
    * etc."""

    def __init__(self, solver=None, ctx=None, logFile=None):
        assert solver is None or ctx is not None
        self.ctx = _get_ctx(ctx)
        self.solver = self.ctx.solver
        self.scopes = 0
        self.assertions_ = [[]]
        self.last_result = None
        self.reset()

    def __del__(self):
        if self.solver is not None:
            self.solver = None
        if self.ctx is not None:
            self.ctx = None
