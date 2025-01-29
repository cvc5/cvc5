#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Aina Niemetz, Makai Mann, Mathias Preiner
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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

    # rounding mode
    rm = tm.mkRoundingMode(RoundingMode.ROUND_NEAREST_TIES_TO_EVEN)

    # create a few single-precision variables
    a = tm.mkConst(fp32, 'a')
    b = tm.mkConst(fp32, 'b')
    c = tm.mkConst(fp32, 'c')
    d = tm.mkConst(fp32, 'd')
    e = tm.mkConst(fp32, 'e')

    print("Show that fused multiplication and addition `(fp.fma RM a b c)`")
    print("is different from `(fp.add RM (fp.mul a b) c)`:")
    slv.push()
    fma = tm.mkTerm(Kind.FLOATINGPOINT_FMA, rm, a, b, c)
    mul = tm.mkTerm(Kind.FLOATINGPOINT_MULT, rm, a, b)
    add = tm.mkTerm(Kind.FLOATINGPOINT_ADD, rm, mul, c)
    slv.assertFormula(tm.mkTerm(Kind.DISTINCT, fma, add))
    print("Expect SAT.")
    print("cvc5:", slv.checkSat())
    print(f'Value of `a`: {slv.getValue(a)}')
    print(f'Value of `b`: {slv.getValue(b)}')
    print(f'Value of `c`: {slv.getValue(c)}')
    print(f'Value of `(fp.fma RNE a b c)`: {slv.getValue(fma)}')
    print(f'Value of `(fp.add RNE (fp.mul a b) c)`: {slv.getValue(add)}')
    print();
    slv.pop();

    print("Show that floating-point addition is not associative:")
    print("(a + (b + c)) != ((a + b) + c)")
    slv.push()
    slv.assertFormula(tm.mkTerm(
      Kind.DISTINCT,
      tm.mkTerm(Kind.FLOATINGPOINT_ADD,
                 rm, a, tm.mkTerm(Kind.FLOATINGPOINT_ADD, rm, b, c)),
       tm.mkTerm(Kind.FLOATINGPOINT_ADD,
                 rm, tm.mkTerm(Kind.FLOATINGPOINT_ADD, rm, a, b), c)))
    print("Expect SAT.")
    print("cvc5:", slv.checkSat())

    print(f'Value of `a`: {slv.getValue(a)}')
    print(f'Value of `b`: {slv.getValue(b)}')
    print(f'Value of `c`: {slv.getValue(c)}')
    print()

    print("Now, restrict `a` to be either NaN or positive infinity:")
    nan = tm.mkFloatingPointNaN(8, 24)
    inf = tm.mkFloatingPointPosInf(8, 24)
    slv.assertFormula(tm.mkTerm(
        Kind.OR, tm.mkTerm(Kind.EQUAL, a, inf), tm.mkTerm(Kind.EQUAL, a, nan)))
    print("Expect SAT.")
    print("cvc5:", slv.checkSat())

    print(f'Value of `a`: {slv.getValue(a)}')
    print(f'Value of `b`: {slv.getValue(b)}')
    print(f'Value of `c`: {slv.getValue(c)}')
    print()
    slv.pop(1)

    print("Now, try to find a (normal) floating-point number that rounds")
    print("to different integer values for different rounding modes:")
    slv.push()
    rtp = tm.mkRoundingMode(RoundingMode.ROUND_TOWARD_POSITIVE)
    rtn = tm.mkRoundingMode(RoundingMode.ROUND_TOWARD_NEGATIVE)
    op = tm.mkOp(Kind.FLOATINGPOINT_TO_UBV, 16)  # (_ fp.to_ubv 16)
    lhs = tm.mkTerm(op, rtp, d)
    rhs = tm.mkTerm(op, rtn, d)
    slv.assertFormula(tm.mkTerm(Kind.FLOATINGPOINT_IS_NORMAL, d))
    slv.assertFormula(tm.mkTerm(Kind.NOT, tm.mkTerm(Kind.EQUAL, lhs, rhs)))

    print("Expect SAT.")
    print("cvc5:", slv.checkSat())

    print("Get value of `d` as floating-point, bit-vector and real:")
    val = slv.getValue(d)
    print(f'Value of `d`: {val}')
    print(f'Value of `((_ fp.to_ubv 16) RTP d)`: {slv.getValue(lhs)}')
    print(f'Value of `((_ fp.to_ubv 16) RTN d)`: {slv.getValue(rhs)}')
    print(f'Value of `(fp.to_real d)`: {slv.getValue(tm.mkTerm(Kind.FLOATINGPOINT_TO_REAL, val))}')
    print()
    slv.pop()

    print("Finally, try to find a floating-point number between positive")
    print("zero and the smallest positive floating-point number:")
    zero = tm.mkFloatingPointPosZero(8, 24)
    smallest = tm.mkFloatingPoint(8, 24, tm.mkBitVector(32, 0b001))
    slv.assertFormula(tm.mkTerm(
        Kind.AND, tm.mkTerm(Kind.FLOATINGPOINT_LT, zero, e),
                  tm.mkTerm(Kind.FLOATINGPOINT_LT, e, smallest)))
    print("Expect UNSAT.")
    print("cvc5:", slv.checkSat())
