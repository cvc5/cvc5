#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Gereon Kremer, Aina Niemetz, Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
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
    slv = cvc5.Solver()
    slv.setLogic("QF_NRAT")

    real = slv.getRealSort()

    # Variables
    x = slv.mkConst(real, "x")
    y = slv.mkConst(real, "y")

    # Helper terms
    two = slv.mkReal(2)
    pi = slv.mkPi()
    twopi = slv.mkTerm(Kind.MULT, two, pi)
    ysq = slv.mkTerm(Kind.MULT, y, y)
    sinx = slv.mkTerm(Kind.SINE, x)

    # Formulas
    x_gt_pi = slv.mkTerm(Kind.GT, x, pi)
    x_lt_tpi = slv.mkTerm(Kind.LT, x, twopi)
    ysq_lt_sinx = slv.mkTerm(Kind.LT, ysq, sinx)
    
    slv.assertFormula(x_gt_pi)
    slv.assertFormula(x_lt_tpi)
    slv.assertFormula(ysq_lt_sinx)

    print("cvc5 should report UNSAT")
    print("Result from cvc5 is:", slv.checkSat())
