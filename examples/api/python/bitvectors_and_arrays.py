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
# A simple demonstration of the solving capabilities of the cvc5
# bit-vector and array solvers through the Python API. This is a direct
# translation of bitvectors_and_arrays-new.cpp.
##

import cvc5
from cvc5 import Kind

import math

if __name__ == "__main__":
    tm = cvc5.TermManager()
    slv = cvc5.Solver(tm)
    slv.setOption("produce-models", "true")
    slv.setOption("output-language", "smtlib")
    slv.setLogic("QF_AUFBV")

    # Consider the following code (where size is some previously defined constant):
    #
    #
    #   Assert (current_array[0] > 0);
    #   for (unsigned i = 1; i < k; ++i) {
    #     current_array[i] = 2 * current_array[i - 1];
    #     Assert (current_array[i-1] < current_array[i]);
    #     }
    #
    # We want to check whether the assertion in the body of the for loop holds
    # throughout the loop.

    # Setting up the problem parameters
    k = 4
    index_size = int(math.ceil(math.log(k, 2)))

    # Sorts
    elementSort = tm.mkBitVectorSort(32)
    indexSort = tm.mkBitVectorSort(index_size)
    arraySort = tm.mkArraySort(indexSort, elementSort)

    # Variables
    current_array = tm.mkConst(arraySort, "current_array")

    # Making a bit-vector constant
    zero = tm.mkBitVector(index_size, 0)

    # Test making a constant array
    constarr0 = tm.mkConstArray(arraySort, tm.mkBitVector(32, 0))

    # Asserting that current_array[0] > 0
    current_array0 = tm.mkTerm(Kind.SELECT, current_array, zero)
    current_array0_gt_0 = tm.mkTerm(Kind.BITVECTOR_SGT,
                                     current_array0,
                                     tm.mkBitVector(32, 0))
    slv.assertFormula(current_array0_gt_0)

    # Building the assertions in the loop unrolling
    index = tm.mkBitVector(index_size, 0)
    old_current = tm.mkTerm(Kind.SELECT, current_array, index)
    two = tm.mkBitVector(32, 2)

    assertions = []
    for i in range(1, k):
        index = tm.mkBitVector(index_size, i)
        new_current = tm.mkTerm(Kind.BITVECTOR_MULT, two, old_current)
        # current[i] = 2*current[i-1]
        current_array = \
                tm.mkTerm(Kind.STORE, current_array, index, new_current)
        # current[i-1] < current[i]
        current_slt_new_current = \
                tm.mkTerm(Kind.BITVECTOR_SLT, old_current, new_current)
        assertions.append(current_slt_new_current)
        old_current = tm.mkTerm(Kind.SELECT, current_array, index)

    query = tm.mkTerm(Kind.NOT, tm.mkTerm(Kind.AND, *assertions))

    print("Asserting {} to cvc5".format(query))
    slv.assertFormula(query)
    print("Expect sat.")
    print("cvc5:", slv.checkSatAssuming(tm.mkTrue()))

    # Getting the model
    print("The satisfying model is: ")
    print(" current_array =", slv.getValue(current_array))
    print(" current_array[0]", slv.getValue(current_array0))
