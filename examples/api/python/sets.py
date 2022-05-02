#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Makai Mann, Aina Niemetz, Mudathir Mohamed
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple demonstration of the solving capabilities of the cvc5 sets solver
# through the Python API. This is a direct translation of sets.cpp.
##

import cvc5
from cvc5 import Kind

if __name__ == "__main__":
    slv = cvc5.Solver()

    # Optionally, set the logic. We need at least UF for equality predicate,
    # integers (LIA) and sets (FS).
    slv.setLogic("QF_UFLIAFS")

    # Produce models
    slv.setOption("produce-models", "true")
    slv.setOption("output-language", "smt2")

    integer = slv.getIntegerSort()
    set_ = slv.mkSetSort(integer)

    # Verify union distributions over intersection
    # (A union B) intersection C = (A intersection C) union (B intersection C)

    A = slv.mkConst(set_, "A")
    B = slv.mkConst(set_, "B")
    C = slv.mkConst(set_, "C")

    unionAB = slv.mkTerm(Kind.SET_UNION, A, B)
    lhs = slv.mkTerm(Kind.SET_INTER, unionAB, C)

    intersectionAC = slv.mkTerm(Kind.SET_INTER, A, C)
    intersectionBC = slv.mkTerm(Kind.SET_INTER, B, C)
    rhs = slv.mkTerm(Kind.SET_UNION, intersectionAC, intersectionBC)

    theorem = slv.mkTerm(Kind.EQUAL, lhs, rhs)

    print("cvc5 reports: {} is {}".format(
        theorem.notTerm(), slv.checkSatAssuming(theorem.notTerm())))

    # Verify emptset is a subset of any set

    A = slv.mkConst(set_, "A")
    emptyset = slv.mkEmptySet(set_)

    theorem = slv.mkTerm(Kind.SET_SUBSET, emptyset, A)

    print("cvc5 reports: {} is {}".format(
        theorem.notTerm(), slv.checkSatAssuming(theorem.notTerm())))

    # Find me an element in 1, 2 intersection 2, 3, if there is one.

    one = slv.mkInteger(1)
    two = slv.mkInteger(2)
    three = slv.mkInteger(3)

    singleton_one = slv.mkTerm(Kind.SET_SINGLETON, one)
    singleton_two = slv.mkTerm(Kind.SET_SINGLETON, two)
    singleton_three = slv.mkTerm(Kind.SET_SINGLETON, three)
    one_two = slv.mkTerm(Kind.SET_UNION, singleton_one, singleton_two)
    two_three = slv.mkTerm(Kind.SET_UNION, singleton_two, singleton_three)
    intersection = slv.mkTerm(Kind.SET_INTER, one_two, two_three)

    x = slv.mkConst(integer, "x")

    e = slv.mkTerm(Kind.SET_MEMBER, x, intersection)

    result = slv.checkSatAssuming(e)

    print("cvc5 reports: {} is {}".format(e, result))

    if result:
        print("For instance, {} is a member".format(slv.getValue(x)))
