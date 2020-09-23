#!/usr/bin/env python
#####################
## bitvectors_and_arrays.py
## Top contributors (to current version):
##   Makai Mann
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
## A simple demonstration of the solving capabilities of the CVC4
## bit-vector and array solvers through the Python API. This is a direct
## translation of bitvectors_and_arrays-new.cpp.
##

import pycvc4
from pycvc4 import kinds

import math

if __name__ == "__main__":
    slv = pycvc4.Solver()
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
    elementSort = slv.mkBitVectorSort(32)
    indexSort = slv.mkBitVectorSort(index_size)
    arraySort = slv.mkArraySort(indexSort, elementSort)

    # Variables
    current_array = slv.mkConst(arraySort, "current_array")

    # Making a bit-vector constant
    zero = slv.mkBitVector(index_size, 0)

    # Test making a constant array
    constarr0 = slv.mkConstArray(arraySort, slv.mkBitVector(32, 0))

    # Asserting that current_array[0] > 0
    current_array0 = slv.mkTerm(kinds.Select, current_array, zero)
    current_array0_gt_0 = slv.mkTerm(kinds.BVSgt,
                                     current_array0,
                                     slv.mkBitVector(32, 0))
    slv.assertFormula(current_array0_gt_0)

    # Building the assertions in the loop unrolling
    index = slv.mkBitVector(index_size, 0)
    old_current = slv.mkTerm(kinds.Select, current_array, index)
    two = slv.mkBitVector(32, 2)

    assertions = []
    for i in range(1, k):
        index = slv.mkBitVector(index_size, i)
        new_current = slv.mkTerm(kinds.BVMult, two, old_current)
        # current[i] = 2*current[i-1]
        current_array = slv.mkTerm(kinds.Store, current_array, index, new_current)
        # current[i-1] < current[i]
        current_slt_new_current = slv.mkTerm(kinds.BVSlt, old_current, new_current)
        assertions.append(current_slt_new_current)
        old_current = slv.mkTerm(kinds.Select, current_array, index)

    query = slv.mkTerm(kinds.Not, slv.mkTerm(kinds.And, assertions))

    print("Asserting {} to CVC4".format(query))
    slv.assertFormula(query)
    print("Expect sat.")
    print("CVC4:", slv.checkSatAssuming(slv.mkTrue()))

    # Getting the model
    print("The satisfying model is: ")
    print(" current_array =", slv.getValue(current_array))
    print(" current_array[0]", slv.getValue(current_array0))
