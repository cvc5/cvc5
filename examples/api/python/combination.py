#!/usr/bin/env python
#####################
## combination.py
## Top contributors (to current version):
##   Makai Mann, Aina Niemetz, Andrew Reynolds
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
## A simple demonstration of the solving capabilities of the CVC4
## combination solver through the Python API. This is a direct translation
## of combination-new.cpp.
##

import pycvc4
from pycvc4 import kinds

def prefixPrintGetValue(slv, t, level=0):
    print("slv.getValue({}): {}".format(t, slv.getValue(t)))
    for c in t:
        prefixPrintGetValue(slv, c, level + 1)

if __name__ == "__main__":
    slv = pycvc4.Solver()
    slv.setOption("produce-models", "true")  # Produce Models
    slv.setOption("output-language", "cvc4") # Set the output-language to CVC's
    slv.setOption("dag-thresh", "0") # Disable dagifying the output
    slv.setOption("output-language", "smt2") # use smt-lib v2 as output language
    slv.setLogic("QF_UFLIRA")

    # Sorts
    u = slv.mkUninterpretedSort("u")
    integer = slv.getIntegerSort()
    boolean = slv.getBooleanSort()
    uToInt = slv.mkFunctionSort(u, integer)
    intPred = slv.mkFunctionSort(integer, boolean)

    # Variables
    x = slv.mkConst(u, "x")
    y = slv.mkConst(u, "y")

    # Functions
    f = slv.mkConst(uToInt, "f")
    p = slv.mkConst(intPred, "p")

    # Constants
    zero = slv.mkReal(0)
    one = slv.mkReal(1)

    # Terms
    f_x = slv.mkTerm(kinds.ApplyUf, f, x)
    f_y = slv.mkTerm(kinds.ApplyUf, f, y)
    sum_ = slv.mkTerm(kinds.Plus, f_x, f_y)
    p_0 = slv.mkTerm(kinds.ApplyUf, p, zero)
    p_f_y = slv.mkTerm(kinds.ApplyUf, p, f_y)

    # Construct the assertions
    assertions = slv.mkTerm(kinds.And,
                            [
                                slv.mkTerm(kinds.Leq, zero, f_x), # 0 <= f(x)
                                slv.mkTerm(kinds.Leq, zero, f_y), # 0 <= f(y)
                                slv.mkTerm(kinds.Leq, sum_, one), # f(x) + f(y) <= 1
                                p_0.notTerm(), # not p(0)
                                p_f_y # p(f(y))
                            ])

    slv.assertFormula(assertions)

    print("Given the following assertions:", assertions, "\n")
    print("Prove x /= y is entailed.\nCVC4: ",
          slv.checkEntailed(slv.mkTerm(kinds.Distinct, x, y)), "\n")

    print("Call checkSat to show that the assertions are satisfiable")
    print("CVC4:", slv.checkSat(), "\n")

    print("Call slv.getValue(...) on terms of interest")
    print("slv.getValue({}): {}".format(f_x, slv.getValue(f_x)))
    print("slv.getValue({}): {}".format(f_y, slv.getValue(f_y)))
    print("slv.getValue({}): {}".format(sum_, slv.getValue(sum_)))
    print("slv.getValue({}): {}".format(p_0, slv.getValue(p_0)))
    print("slv.getValue({}): {}".format(p_f_y, slv.getValue(p_f_y)), "\n")

    print("Alternatively, iterate over assertions and call"
          " slv.getValue(...) on all terms")
    prefixPrintGetValue(slv, assertions)

    print("Alternatively, print the model", "\n")
    slv.printModel()

    print()
    print("You can also use nested loops to iterate over terms")
    for a in assertions:
        print("term:", a)
        for t in a:
            print(" + child: ", t)

    print()
