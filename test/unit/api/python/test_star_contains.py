###############################################################################
# Top contributors (to current version):
#   Mudathir Mohamed
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
##

import pytest
import cvc5
from cvc5 import Sort, Term, Kind


@pytest.fixture
def tm():
    return cvc5.TermManager()


@pytest.fixture
def solver(tm):
    return cvc5.Solver(tm)


def test_disjoint_union_unsat(tm, solver):
    solver.setOption("produce-models", "true")
    solver.setOption("trace", "liastar-ext")
    integer = tm.getIntegerSort()
    zero = tm.mkInteger(0)
    a = tm.mkConst(integer, "a")
    b = tm.mkConst(integer, "b")
    c = tm.mkConst(integer, "c")
    a_plus_b = tm.mkTerm(Kind.ADD, a, b)
    distinct = tm.mkTerm(Kind.DISTINCT, c, a_plus_b)
    solver.assertFormula(distinct)
    a_nonnegative = tm.mkTerm(Kind.GEQ, a, zero)
    b_nonnegative = tm.mkTerm(Kind.GEQ, b, zero)
    c_nonnegative = tm.mkTerm(Kind.GEQ, c, zero)
    nonnegative = tm.mkTerm(Kind.AND, a_nonnegative, b_nonnegative, c_nonnegative)
    solver.assertFormula(nonnegative)

    x = tm.mkVar(integer, "x")
    y = tm.mkVar(integer, "y")
    z = tm.mkVar(integer, "z")
    x_nonnegative = tm.mkTerm(Kind.GEQ, x, zero)
    y_nonnegative = tm.mkTerm(Kind.GEQ, y, zero)
    z_nonnegative = tm.mkTerm(Kind.GEQ, z, zero)

    vars = tm.mkTerm(Kind.VARIABLE_LIST, x, y, z)
    tuple = tm.mkTuple([a, b, c])

    plus_x_y = tm.mkTerm(Kind.ADD, x, y)
    equal = z.eqTerm(plus_x_y)
    body = tm.mkTerm(Kind.AND, x_nonnegative, y_nonnegative, z_nonnegative, equal)
    star_contains = tm.mkTerm(Kind.STAR_CONTAINS, vars, body, tuple)
    solver.assertFormula(star_contains)
    r = solver.checkSat()
    assert r.isUnsat()
