#!/usr/bin/env python
#####################
## floating_point.py
## Top contributors (to current version):
##   Makai Mann, Andres Noetzli
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
## A simple demonstration of the solving capabilities of the CVC4
## floating point solver through the Python API contributed by Eva
## Darulova. This requires building CVC4 with symfpu.
##

import pycvc4
from pycvc4 import kinds

if __name__ == "__main__":
    slv = pycvc4.Solver()

    if not slv.supportsFloatingPoint():
        # CVC4 must be built with SymFPU to support the theory of
        # floating-point numbers
        print("CVC4 was not built with floating-point support.")
        exit()

    slv.setOption("produce-models", "true")
    slv.setLogic("QF_FP")

    # single 32-bit precision
    fp32 = slv.mkFloatingPointSort(8, 24)

    # the standard rounding mode
    rm = slv.mkRoundingMode(pycvc4.RoundNearestTiesToEven)

    # create a few single-precision variables
    x = slv.mkConst(fp32, 'x')
    y = slv.mkConst(fp32, 'y')
    z = slv.mkConst(fp32, 'z')

    # check floating-point arithmetic is commutative, i.e. x + y == y + x
    commutative = slv.mkTerm(kinds.FPEq, slv.mkTerm(kinds.FPPlus, rm, x, y), slv.mkTerm(kinds.FPPlus, rm, y, x))

    slv.push()
    slv.assertFormula(slv.mkTerm(kinds.Not, commutative))
    print("Checking floating-point commutativity")
    print("Expect SAT (property does not hold for NaN and Infinities).")
    print("CVC4:", slv.checkSat())
    print("Model for x:", slv.getValue(x))
    print("Model for y:", slv.getValue(y))

    # disallow NaNs and Infinities
    slv.assertFormula(slv.mkTerm(kinds.Not, slv.mkTerm(kinds.FPIsNan, x)))
    slv.assertFormula(slv.mkTerm(kinds.Not, slv.mkTerm(kinds.FPIsInf, x)))
    slv.assertFormula(slv.mkTerm(kinds.Not, slv.mkTerm(kinds.FPIsNan, y)))
    slv.assertFormula(slv.mkTerm(kinds.Not, slv.mkTerm(kinds.FPIsInf, y)))

    print("Checking floating-point commutativity assuming x and y are not NaN or Infinity")
    print("Expect UNSAT.")
    print("CVC4:", slv.checkSat())

    # check floating-point arithmetic is not associative
    slv.pop()

    # constrain x, y, z between -3.14 and 3.14 (also disallows NaN and infinity)
    a = slv.mkFloatingPoint(8, 24, slv.mkBitVector("11000000010010001111010111000011", 2))  # -3.14
    b = slv.mkFloatingPoint(8, 24, slv.mkBitVector("01000000010010001111010111000011", 2))  # 3.14

    bounds_x = slv.mkTerm(kinds.And, slv.mkTerm(kinds.FPLeq, a, x), slv.mkTerm(kinds.FPLeq, x, b))
    bounds_y = slv.mkTerm(kinds.And, slv.mkTerm(kinds.FPLeq, a, y), slv.mkTerm(kinds.FPLeq, y, b))
    bounds_z = slv.mkTerm(kinds.And, slv.mkTerm(kinds.FPLeq, a, z), slv.mkTerm(kinds.FPLeq, z, b))
    slv.assertFormula(slv.mkTerm(kinds.And, slv.mkTerm(kinds.And, bounds_x, bounds_y), bounds_z))

    # (x + y) + z == x + (y + z)
    lhs = slv.mkTerm(kinds.FPPlus, rm, slv.mkTerm(kinds.FPPlus, rm, x, y), z)
    rhs = slv.mkTerm(kinds.FPPlus, rm, x, slv.mkTerm(kinds.FPPlus, rm, y, z))
    associative = slv.mkTerm(kinds.Not, slv.mkTerm(kinds.FPEq, lhs, rhs))

    slv.assertFormula(associative)

    print("Checking floating-point associativity")
    print("Expect SAT.")
    print("CVC4:", slv.checkSat())
    print("Model for x:", slv.getValue(x))
    print("Model for y:", slv.getValue(y))
    print("Model for z:", slv.getValue(z))
