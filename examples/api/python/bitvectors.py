#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Makai Mann, Aina Niemetz, Andrew Reynolds
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple demonstration of the solving capabilities of the cvc5 bit-vector
# solver through the Python API. This is a direct translation of
# bitvectors-new.cpp.
##

import cvc5
from cvc5 import Kind

if __name__ == "__main__":
    slv = cvc5.Solver()
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
    # We will use cvc5 to prove that the three pieces of code above are all
    # equivalent by encoding the problem in the bit-vector theory.

    # Creating a bit-vector type of width 32
    bitvector32 = slv.mkBitVectorSort(32)

    # Variables
    x = slv.mkConst(bitvector32, "x")
    a = slv.mkConst(bitvector32, "a")
    b = slv.mkConst(bitvector32, "b")

    # First encode the assumption that x must be equal to a or b
    x_eq_a = slv.mkTerm(Kind.EQUAL, x, a)
    x_eq_b = slv.mkTerm(Kind.EQUAL, x, b)
    assumption = slv.mkTerm(Kind.OR, x_eq_a, x_eq_b)

    # Assert the assumption
    slv.assertFormula(assumption)

    # Introduce a new variable for the new value of x after assignment.
    # x after executing code (0)
    new_x = slv.mkConst(bitvector32, "new_x")
    # x after executing code (1) or (2)
    new_x_ = slv.mkConst(bitvector32, "new_x_")

    # Encoding code (0)
    # new_x = x == a ? b : a
    ite = slv.mkTerm(Kind.ITE, x_eq_a, b, a)
    assignment0 = slv.mkTerm(Kind.EQUAL, new_x, ite)

    # Assert the encoding of code (0)
    print("Asserting {} to cvc5".format(assignment0))
    slv.assertFormula(assignment0)
    print("Pushing a new context.")
    slv.push()

    # Encoding code (1)
    # new_x_ = a xor b xor x
    a_xor_b_xor_x = slv.mkTerm(Kind.BITVECTOR_XOR, a, b, x)
    assignment1 = slv.mkTerm(Kind.EQUAL, new_x_, a_xor_b_xor_x)

    # Assert encoding to cvc5 in current context
    print("Asserting {} to cvc5".format(assignment1))
    slv.assertFormula(assignment1)
    new_x_eq_new_x_ = slv.mkTerm(Kind.EQUAL, new_x, new_x_)

    print("Checking sat assuming:", new_x_eq_new_x_.notTerm())
    print("Expect UNSAT.")
    print("cvc5:", slv.checkSatAssuming(new_x_eq_new_x_.notTerm()))
    print("Popping context.")
    slv.pop()

    # Encoding code (2)
    # new_x_ = a + b - x
    a_plus_b = slv.mkTerm(Kind.BITVECTOR_ADD, a, b)
    a_plus_b_minus_x = slv.mkTerm(Kind.BITVECTOR_SUB, a_plus_b, x)
    assignment2 = slv.mkTerm(Kind.EQUAL, new_x_, a_plus_b_minus_x)

    # Assert encoding to cvc5 in current context
    print("Asserting {} to cvc5".format(assignment2))
    slv.assertFormula(assignment2)

    print("Checking sat assuming:", new_x_eq_new_x_.notTerm())
    print("Expect UNSAT.")
    print("cvc5:", slv.checkSatAssuming(new_x_eq_new_x_.notTerm()))


    x_neq_x = slv.mkTerm(Kind.EQUAL, x, x).notTerm()
    query = slv.mkTerm(Kind.AND, new_x_eq_new_x_, x_neq_x)
    print("Check sat assuming: ", query.notTerm())
    print("Expect SAT.")
    print("cvc5:", slv.checkSatAssuming(query.notTerm()))

    # Assert that a is odd
    extract_op = slv.mkOp(Kind.BITVECTOR_EXTRACT, 0, 0)
    lsb_of_a = slv.mkTerm(extract_op, a)
    print("Sort of {} is {}".format(lsb_of_a, lsb_of_a.getSort()))
    a_odd = slv.mkTerm(Kind.EQUAL, lsb_of_a, slv.mkBitVector(1, 1))
    print("Assert", a_odd)
    print("Check satisifiability")
    slv.assertFormula(a_odd)
    print("Expect sat")
    print("cvc5:", slv.checkSat())
