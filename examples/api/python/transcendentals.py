#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Makai Mann, Mudathir Mohamed, Aina Niemetz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple demonstration of the transcendental extension.
##

import pycvc5
from pycvc5 import kinds

if __name__ == "__main__":
    slv = pycvc5.Solver()
    slv.setLogic("QF_NRAT")

    real = slv.getRealSort()

    # Variables
    x = slv.mkConst(real, "x")
    y = slv.mkConst(real, "y")

    # Helper terms
    two = slv.mkReal(2)
    pi = slv.mkPi()
    twopi = slv.mkTerm(kinds.Mult, two, pi)
    ysq = slv.mkTerm(kinds.Mult, y, y)
    sinx = slv.mkTerm(kinds.Sine, x)

    # Formulas
    x_gt_pi = slv.mkTerm(kinds.Gt, x, pi)
    x_lt_tpi = slv.mkTerm(kinds.Lt, x, twopi)
    ysq_lt_sinx = slv.mkTerm(kinds.Lt, ysq, sinx)
    
    slv.assertFormula(x_gt_pi)
    slv.assertFormula(x_lt_tpi)
    slv.assertFormula(ysq_lt_sinx)

    print("cvc5 should report UNSAT")
    print("Result from cvc5 is:", slv.checkSat())
