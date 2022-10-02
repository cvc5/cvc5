#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Aina Niemetz, Makai Mann, Mathias Preiner
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
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
    slv = cvc5.Solver()

    slv.setOption("produce-models", "true")
    slv.setLogic("QF_FP")

    # single 32-bit precision
    fp32 = slv.mkFloatingPointSort(8, 24)

    # the standard rounding mode
    rm = slv.mkRoundingMode(RoundingMode.ROUND_NEAREST_TIES_TO_EVEN)

    # create a few single-precision variables
    x = slv.mkConst(fp32, 'x')
    y = slv.mkConst(fp32, 'y')
    z = slv.mkConst(fp32, 'z')

    # check floating-point arithmetic is commutative, i.e. x + y == y + x
    commutative = slv.mkTerm(
            Kind.FLOATINGPOINT_EQ,
            slv.mkTerm(Kind.FLOATINGPOINT_ADD, rm, x, y),
            slv.mkTerm(Kind.FLOATINGPOINT_ADD, rm, y, x))

    slv.push()
    slv.assertFormula(slv.mkTerm(Kind.NOT, commutative))
    print("Checking floating-point commutativity")
    print("Expect SAT (property does not hold for NaN and Infinities).")
    print("cvc5:", slv.checkSat())
    print("Model for x:", slv.getValue(x))
    print("Model for y:", slv.getValue(y))

    # disallow NaNs and Infinities
    slv.assertFormula(slv.mkTerm(
        Kind.NOT, slv.mkTerm(Kind.FLOATINGPOINT_IS_NAN, x)))
    slv.assertFormula(slv.mkTerm(
        Kind.NOT, slv.mkTerm(Kind.FLOATINGPOINT_IS_INF, x)))
    slv.assertFormula(slv.mkTerm(
        Kind.NOT, slv.mkTerm(Kind.FLOATINGPOINT_IS_NAN, y)))
    slv.assertFormula(slv.mkTerm(
        Kind.NOT, slv.mkTerm(Kind.FLOATINGPOINT_IS_INF, y)))

    print("Checking floating-point commutativity assuming x and y are not NaN or Infinity")
    print("Expect UNSAT.")
    print("cvc5:", slv.checkSat())

    # check floating-point arithmetic is not associative
    slv.pop()

    # constrain x, y, z between -3.14 and 3.14 (also disallows NaN and infinity)
    a = slv.mkFloatingPoint(
            8,
            24,
            slv.mkBitVector(32, "11000000010010001111010111000011", 2)) # -3.14
    b = slv.mkFloatingPoint(
            8,
            24,
            slv.mkBitVector(32, "01000000010010001111010111000011", 2))  # 3.14

    bounds_x = slv.mkTerm(
            Kind.AND,
            slv.mkTerm(Kind.FLOATINGPOINT_LEQ, a, x),
            slv.mkTerm(Kind.FLOATINGPOINT_LEQ, x, b))
    bounds_y = slv.mkTerm(
            Kind.AND,
            slv.mkTerm(Kind.FLOATINGPOINT_LEQ, a, y),
            slv.mkTerm(Kind.FLOATINGPOINT_LEQ, y, b))
    bounds_z = slv.mkTerm(
            Kind.AND,
            slv.mkTerm(Kind.FLOATINGPOINT_LEQ, a, z),
            slv.mkTerm(Kind.FLOATINGPOINT_LEQ, z, b))
    slv.assertFormula(slv.mkTerm(
        Kind.AND, slv.mkTerm(Kind.AND, bounds_x, bounds_y), bounds_z))

    # (x + y) + z == x + (y + z)
    lhs = slv.mkTerm(
            Kind.FLOATINGPOINT_ADD,
            rm,
            slv.mkTerm(Kind.FLOATINGPOINT_ADD, rm, x, y),
            z)
    rhs = slv.mkTerm(
            Kind.FLOATINGPOINT_ADD,
            rm,
            x,
            slv.mkTerm(Kind.FLOATINGPOINT_ADD, rm, y, z))
    associative = slv.mkTerm(
            Kind.NOT,
            slv.mkTerm(Kind.FLOATINGPOINT_EQ, lhs, rhs))

    slv.assertFormula(associative)

    print("Checking floating-point associativity")
    print("Expect SAT.")
    print("cvc5:", slv.checkSat())
    print("Model for x:", slv.getValue(x))
    print("Model for y:", slv.getValue(y))
    print("Model for z:", slv.getValue(z))
