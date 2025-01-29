#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Yoni Zohar
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple demonstration of the solving capabilities of the cvc5 uf solver.
##

import cvc5
from cvc5 import Kind

if __name__ == "__main__":
    tm = cvc5.TermManager()
    slv = cvc5.Solver(tm)
    slv.setLogic("QF_UF")

    # Sorts
    u = tm.mkUninterpretedSort("U")
    integer = tm.getIntegerSort()
    boolean = tm.getBooleanSort()
    uTou = tm.mkFunctionSort(u, u)
    uPred = tm.mkFunctionSort(u, boolean)

    # Variables
    x = tm.mkConst(u, "x")
    y = tm.mkConst(u, "y")

    # Functions
    f = tm.mkConst(uTou, "f")
    p = tm.mkConst(uPred, "p")


    # Terms
    f_x = tm.mkTerm(Kind.APPLY_UF, f, x)
    f_y = tm.mkTerm(Kind.APPLY_UF, f, y)
    p_f_x = tm.mkTerm(Kind.APPLY_UF, p, f_x)
    p_f_y = tm.mkTerm(Kind.APPLY_UF, p, f_y)

    # Construct the assertions
    assertions = tm.mkTerm(Kind.AND,
                            tm.mkTerm(Kind.EQUAL, x, f_x),
                            tm.mkTerm(Kind.EQUAL, y, f_y), 
                            p_f_x.notTerm(),
                            p_f_y)

    slv.assertFormula(assertions)
    assert(slv.checkSat().isSat())

