#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Aina Niemetz, Makai Mann, Mathias Preiner
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple demonstration of the solving capabilities of the cvc5
# floating point solver through the Python API contributed by Eva
# Darulova. This requires building cvc5 with symfpu.
##

import cvc5
from cvc5 import Kind, RoundingMode

if __name__ == "__main__":
    tm = cvc5.TermManager()
    slv = cvc5.Solver(tm)

    slv.setOption("produce-models", "true")
    slv.setLogic("QF_FP")

    # single 32-bit precision
    fp32 = tm.mkFloatingPointSort(8, 24)

    # the standard rounding mode
    rm = tm.mkRoundingMode(RoundingMode.ROUND_NEAREST_TIES_TO_EVEN)

    # create a few single-precision variables
    x = tm.mkConst(fp32, 'x')
    y = tm.mkConst(fp32, 'y')
    z = tm.mkConst(fp32, 'z')

    # check floating-point arithmetic is commutative, i.e. x + y == y + x
    commutative = tm.mkTerm(
            Kind.FLOATINGPOINT_EQ,
            tm.mkTerm(Kind.FLOATINGPOINT_ADD, rm, x, y),
            tm.mkTerm(Kind.FLOATINGPOINT_ADD, rm, y, x))

    slv.push()
    slv.assertFormula(tm.mkTerm(Kind.NOT, commutative))
    print("Checking floating-point commutativity")
    print("Expect SAT (property does not hold for NaN and Infinities).")
    print("cvc5:", slv.checkSat())
    print("Model for x:", slv.getValue(x))
    print("Model for y:", slv.getValue(y))

    # disallow NaNs and Infinities
    slv.assertFormula(tm.mkTerm(
        Kind.NOT, tm.mkTerm(Kind.FLOATINGPOINT_IS_NAN, x)))
    slv.assertFormula(tm.mkTerm(
        Kind.NOT, tm.mkTerm(Kind.FLOATINGPOINT_IS_INF, x)))
    slv.assertFormula(tm.mkTerm(
        Kind.NOT, tm.mkTerm(Kind.FLOATINGPOINT_IS_NAN, y)))
    slv.assertFormula(tm.mkTerm(
        Kind.NOT, tm.mkTerm(Kind.FLOATINGPOINT_IS_INF, y)))

    print("Checking floating-point commutativity assuming x and y are not NaN or Infinity")
    print("Expect UNSAT.")
    print("cvc5:", slv.checkSat())

    # check floating-point arithmetic is not associative
    slv.pop()

    # constrain x, y, z between -3.14 and 3.14 (also disallows NaN and infinity)
    a = tm.mkFloatingPoint(
            8,
            24,
            tm.mkBitVector(32, "11000000010010001111010111000011", 2)) # -3.14
    b = tm.mkFloatingPoint(
            8,
            24,
            tm.mkBitVector(32, "01000000010010001111010111000011", 2))  # 3.14

    bounds_x = tm.mkTerm(
            Kind.AND,
            tm.mkTerm(Kind.FLOATINGPOINT_LEQ, a, x),
            tm.mkTerm(Kind.FLOATINGPOINT_LEQ, x, b))
    bounds_y = tm.mkTerm(
            Kind.AND,
            tm.mkTerm(Kind.FLOATINGPOINT_LEQ, a, y),
            tm.mkTerm(Kind.FLOATINGPOINT_LEQ, y, b))
    bounds_z = tm.mkTerm(
            Kind.AND,
            tm.mkTerm(Kind.FLOATINGPOINT_LEQ, a, z),
            tm.mkTerm(Kind.FLOATINGPOINT_LEQ, z, b))
    slv.assertFormula(tm.mkTerm(
        Kind.AND, tm.mkTerm(Kind.AND, bounds_x, bounds_y), bounds_z))

    # (x + y) + z == x + (y + z)
    lhs = tm.mkTerm(
            Kind.FLOATINGPOINT_ADD,
            rm,
            tm.mkTerm(Kind.FLOATINGPOINT_ADD, rm, x, y),
            z)
    rhs = tm.mkTerm(
            Kind.FLOATINGPOINT_ADD,
            rm,
            x,
            tm.mkTerm(Kind.FLOATINGPOINT_ADD, rm, y, z))
    associative = tm.mkTerm(
            Kind.NOT,
            tm.mkTerm(Kind.FLOATINGPOINT_EQ, lhs, rhs))

    slv.assertFormula(associative)

    print("Checking floating-point associativity")
    print("Expect SAT.")
    print("cvc5:", slv.checkSat())
    print("Model for x:", slv.getValue(x))
    print("Model for y:", slv.getValue(y))
    print("Model for z:", slv.getValue(z))
