#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Makai Mann, Aina Niemetz, Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple demonstration of the solving capabilities of the cvc5 combination
# solver through the Python API. This is a direct translation of
# combination-new.cpp.
##

import cvc5
from cvc5 import Kind

def prefixPrintGetValue(slv, t, level=0):
    print("slv.getValue({}): {}".format(t, slv.getValue(t)))
    for c in t:
        prefixPrintGetValue(slv, c, level + 1)

if __name__ == "__main__":
    tm = cvc5.TermManager()
    slv = cvc5.Solver(tm)
    slv.setOption("produce-models", "true")  # Produce Models
    slv.setOption("dag-thresh", "0") # Disable dagifying the output
    slv.setOption("output-language", "smt2") # use smt-lib v2 as output language
    slv.setLogic("QF_UFLIRA")

    # Sorts
    u = tm.mkUninterpretedSort("u")
    integer = tm.getIntegerSort()
    boolean = tm.getBooleanSort()
    uToInt = tm.mkFunctionSort(u, integer)
    intPred = tm.mkFunctionSort(integer, boolean)

    # Variables
    x = tm.mkConst(u, "x")
    y = tm.mkConst(u, "y")

    # Functions
    f = tm.mkConst(uToInt, "f")
    p = tm.mkConst(intPred, "p")

    # Constants
    zero = tm.mkInteger(0)
    one = tm.mkInteger(1)

    # Terms
    f_x = tm.mkTerm(Kind.APPLY_UF, f, x)
    f_y = tm.mkTerm(Kind.APPLY_UF, f, y)
    sum_ = tm.mkTerm(Kind.ADD, f_x, f_y)
    p_0 = tm.mkTerm(Kind.APPLY_UF, p, zero)
    p_f_y = tm.mkTerm(Kind.APPLY_UF, p, f_y)

    # Construct the assertions
    assertions = tm.mkTerm(Kind.AND,
                            tm.mkTerm(Kind.LEQ, zero, f_x), # 0 <= f(x)
                            tm.mkTerm(Kind.LEQ, zero, f_y), # 0 <= f(y)
                            tm.mkTerm(Kind.LEQ, sum_, one), # f(x) + f(y) <= 1
                            p_0.notTerm(), # not p(0)
                            p_f_y # p(f(y))
                            )

    slv.assertFormula(assertions)

    print("Given the following assertions:", assertions, "\n")
    print("Prove x /= y is entailed.\ncvc5: ",
          slv.checkSatAssuming(tm.mkTerm(Kind.EQUAL, x, y)), "\n")

    print("Call checkSat to show that the assertions are satisfiable")
    print("cvc5:", slv.checkSat(), "\n")

    print("Call slv.getValue(...) on terms of interest")
    print("slv.getValue({}): {}".format(f_x, slv.getValue(f_x)))
    print("slv.getValue({}): {}".format(f_y, slv.getValue(f_y)))
    print("slv.getValue({}): {}".format(sum_, slv.getValue(sum_)))
    print("slv.getValue({}): {}".format(p_0, slv.getValue(p_0)))
    print("slv.getValue({}): {}".format(p_f_y, slv.getValue(p_f_y)), "\n")

    print("Alternatively, iterate over assertions and call"
          " slv.getValue(...) on all terms")
    prefixPrintGetValue(slv, assertions)

    print()
    print("You can also use nested loops to iterate over terms")
    for a in assertions:
        print("term:", a)
        for t in a:
            print(" + child: ", t)

    print()
