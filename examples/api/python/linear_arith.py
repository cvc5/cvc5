#!/usr/bin/env python
#####################
## linear_arith.py
## Top contributors (to current version):
##   Makai Mann, Aina Niemetz
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
## A simple demonstration of the solving capabilities of the CVC4
## linear arithmetic solver through the Python API. This is a direct
## translation of linear_arith-new.cpp.
##

import pycvc4
from pycvc4 import kinds

if __name__ == "__main__":
    slv = pycvc4.Solver()
    slv.setLogic("QF_LIRA")

    # Prove that if given x (Integer) and y (Real) and some constraints
    # then the maximum value of y - x is 2/3

    # Sorts
    real = slv.getRealSort()
    integer = slv.getIntegerSort()

    # Variables
    x = slv.mkConst(integer, "x")
    y = slv.mkConst(real, "y")

    # Constants
    three = slv.mkReal(3)
    neg2 = slv.mkReal(-2)
    two_thirds = slv.mkReal(2, 3)

    # Terms
    three_y = slv.mkTerm(kinds.Mult, three, y)
    diff = slv.mkTerm(kinds.Minus, y, x)

    # Formulas
    x_geq_3y = slv.mkTerm(kinds.Geq, x, three_y)
    x_leq_y = slv.mkTerm(kinds.Leq, x ,y)
    neg2_lt_x = slv.mkTerm(kinds.Lt, neg2, x)

    assertions = slv.mkTerm(kinds.And, x_geq_3y, x_leq_y, neg2_lt_x)

    print("Given the assertions", assertions)
    slv.assertFormula(assertions)

    slv.push()
    diff_leq_two_thirds = slv.mkTerm(kinds.Leq, diff, two_thirds)
    print("Prove that", diff_leq_two_thirds, "with CVC4")
    print("CVC4 should report ENTAILED")
    print("Result from CVC4 is:",
          slv.checkEntailed(diff_leq_two_thirds))
    slv.pop()

    print()

    slv.push()
    diff_is_two_thirds = slv.mkTerm(kinds.Equal, diff, two_thirds)
    slv.assertFormula(diff_is_two_thirds)
    print("Show that the assertions are consistent with\n", diff_is_two_thirds, "with CVC4")
    print("CVC4 should report SAT")
    print("Result from CVC4 is:", slv.checkSat())
    slv.pop()
