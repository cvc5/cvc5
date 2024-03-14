#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Gereon Kremer, Aina Niemetz, Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple demonstration of the transcendental extension.
##

import cvc5
from cvc5 import Kind

if __name__ == "__main__":
    tm = cvc5.TermManager()
    slv = cvc5.Solver(tm)
    slv.setLogic("QF_NRAT")

    real = tm.getRealSort()

    # Variables
    x = tm.mkConst(real, "x")
    y = tm.mkConst(real, "y")

    # Helper terms
    two = tm.mkReal(2)
    pi = tm.mkPi()
    twopi = tm.mkTerm(Kind.MULT, two, pi)
    ysq = tm.mkTerm(Kind.MULT, y, y)
    sinx = tm.mkTerm(Kind.SINE, x)

    # Formulas
    x_gt_pi = tm.mkTerm(Kind.GT, x, pi)
    x_lt_tpi = tm.mkTerm(Kind.LT, x, twopi)
    ysq_lt_sinx = tm.mkTerm(Kind.LT, ysq, sinx)
    
    slv.assertFormula(x_gt_pi)
    slv.assertFormula(x_lt_tpi)
    slv.assertFormula(ysq_lt_sinx)

    print("cvc5 should report UNSAT")
    print("Result from cvc5 is:", slv.checkSat())
