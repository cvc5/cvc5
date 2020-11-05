#!/usr/bin/env python
#####################
## bitvectors.py
## Top contributors (to current version):
##   Makai Mann, Aina Niemetz
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
## A simple demonstration of the solving capabilities of the CVC4
## bit-vector solver through the Python API. This is a direct translation
## of bitvectors-new.cpp.
##

import pycvc4
from pycvc4 import kinds

if __name__ == "__main__":
    slv = pycvc4.Solver()
    slv.setLogic("QF_BV") # Set the logic
    # The following example has been adapted from the book A Hacker's Delight by
    # Henry S. Warren.
    #
    # Given a variable x that can only have two values, a or b. We want to
    # assign to x a value other than the current one. The straightforward code
    # to do that is:
    #
    #(0) if (x == a ) x = b;
    #    else x = a;
    #
    # Two more efficient yet equivalent methods are:
    #
    #(1) x = a xor b xor x;
    #
    #(2) x = a + b - x;
    #
    # We will use CVC4 to prove that the three pieces of code above are all
    # equivalent by encoding the problem in the bit-vector theory.

    # Creating a bit-vector type of width 32
    bitvector32 = slv.mkBitVectorSort(32)

    # Variables
    x = slv.mkConst(bitvector32, "x")
    a = slv.mkConst(bitvector32, "a")
    b = slv.mkConst(bitvector32, "b")

    # First encode the assumption that x must be equal to a or b
    x_eq_a = slv.mkTerm(kinds.Equal, x, a)
    x_eq_b = slv.mkTerm(kinds.Equal, x, b)
    assumption = slv.mkTerm(kinds.Or, x_eq_a, x_eq_b)

    # Assert the assumption
    slv.assertFormula(assumption)

    # Introduce a new variable for the new value of x after assignment.
    # x after executing code (0)
    new_x = slv.mkConst(bitvector32, "new_x")
    # x after executing code (1) or (2)
    new_x_ = slv.mkConst(bitvector32, "new_x_")

    # Encoding code (0)
    # new_x = x == a ? b : a
    ite = slv.mkTerm(kinds.Ite, x_eq_a, b, a)
    assignment0 = slv.mkTerm(kinds.Equal, new_x, ite)

    # Assert the encoding of code (0)
    print("Asserting {} to CVC4".format(assignment0))
    slv.assertFormula(assignment0)
    print("Pushing a new context.")
    slv.push()

    # Encoding code (1)
    # new_x_ = a xor b xor x
    a_xor_b_xor_x = slv.mkTerm(kinds.BVXor, a, b, x)
    assignment1 = slv.mkTerm(kinds.Equal, new_x_, a_xor_b_xor_x)

    # Assert encoding to CVC4 in current context
    print("Asserting {} to CVC4".format(assignment1))
    slv.assertFormula(assignment1)
    new_x_eq_new_x_ = slv.mkTerm(kinds.Equal, new_x, new_x_)

    print("Checking entailment assuming:", new_x_eq_new_x_)
    print("Expect ENTAILED.")
    print("CVC4:", slv.checkEntailed(new_x_eq_new_x_))
    print("Popping context.")
    slv.pop()

    # Encoding code (2)
    # new_x_ = a + b - x
    a_plus_b = slv.mkTerm(kinds.BVPlus, a, b)
    a_plus_b_minus_x = slv.mkTerm(kinds.BVSub, a_plus_b, x)
    assignment2 = slv.mkTerm(kinds.Equal, new_x_, a_plus_b_minus_x)

    # Assert encoding to CVC4 in current context
    print("Asserting {} to CVC4".format(assignment2))
    slv.assertFormula(assignment2)

    print("Checking entailment assuming:", new_x_eq_new_x_)
    print("Expect ENTAILED.")
    print("CVC4:", slv.checkEntailed(new_x_eq_new_x_))


    x_neq_x = slv.mkTerm(kinds.Equal, x, x).notTerm()
    v = [new_x_eq_new_x_, x_neq_x]
    print("Check entailment assuming: ", v)
    print("Expect NOT_ENTAILED.")
    print("CVC4:", slv.checkEntailed(v))

    # Assert that a is odd
    extract_op = slv.mkOp(kinds.BVExtract, 0, 0)
    lsb_of_a = slv.mkTerm(extract_op, a)
    print("Sort of {} is {}".format(lsb_of_a, lsb_of_a.getSort()))
    a_odd = slv.mkTerm(kinds.Equal, lsb_of_a, slv.mkBitVector(1, 1))
    print("Assert", a_odd)
    print("Check satisifiability")
    slv.assertFormula(a_odd)
    print("Expect sat")
    print("CVC4:", slv.checkSat())
