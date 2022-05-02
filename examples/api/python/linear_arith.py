#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Makai Mann, Aina Niemetz, Mathias Preiner
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple demonstration of the solving capabilities of the cvc5 linear
# arithmetic solver through the Python API. This is a direct translation of
# linear_arith-new.cpp.
##

import cvc5
from cvc5 import Kind

if __name__ == "__main__":
    slv = cvc5.Solver()
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
    three = slv.mkInteger(3)
    neg2 = slv.mkInteger(-2)
    two_thirds = slv.mkReal(2, 3)

    # Terms
    three_y = slv.mkTerm(Kind.MULT, three, y)
    diff = slv.mkTerm(Kind.SUB, y, x)

    # Formulas
    x_geq_3y = slv.mkTerm(Kind.GEQ, x, three_y)
    x_leq_y = slv.mkTerm(Kind.LEQ, x ,y)
    neg2_lt_x = slv.mkTerm(Kind.LT, neg2, x)

    assertions = slv.mkTerm(Kind.AND, x_geq_3y, x_leq_y, neg2_lt_x)

    print("Given the assertions", assertions)
    slv.assertFormula(assertions)

    slv.push()
    diff_leq_two_thirds = slv.mkTerm(Kind.LEQ, diff, two_thirds)
    print("Prove that", diff_leq_two_thirds, "with cvc5")
    print("cvc5 should report UNSAT")
    print("Result from cvc5 is:",
          slv.checkSatAssuming(diff_leq_two_thirds.notTerm()))
    slv.pop()

    print()

    slv.push()
    diff_is_two_thirds = slv.mkTerm(Kind.EQUAL, diff, two_thirds)
    slv.assertFormula(diff_is_two_thirds)
    print("Show that the assertions are consistent with\n", diff_is_two_thirds, "with cvc5")
    print("cvc5 should report SAT")
    print("Result from cvc5 is:", slv.checkSat())
    slv.pop()
