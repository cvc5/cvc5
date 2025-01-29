#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Aina Niemetz, Makai Mann, Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
    tm = cvc5.TermManager()
    slv = cvc5.Solver(tm)

    # Optionally, set the logic. We need at least UF for equality predicate,
    # integers (LIA) and sets (FS).
    slv.setLogic("QF_UFLIAFS")

    # Produce models
    slv.setOption("produce-models", "true")
    slv.setOption("output-language", "smt2")

    integer = tm.getIntegerSort()
    set_ = tm.mkSetSort(integer)

    # Verify union distributions over intersection
    # (A union B) intersection C = (A intersection C) union (B intersection C)

    A = tm.mkConst(set_, "A")
    B = tm.mkConst(set_, "B")
    C = tm.mkConst(set_, "C")

    unionAB = tm.mkTerm(Kind.SET_UNION, A, B)
    lhs = tm.mkTerm(Kind.SET_INTER, unionAB, C)

    intersectionAC = tm.mkTerm(Kind.SET_INTER, A, C)
    intersectionBC = tm.mkTerm(Kind.SET_INTER, B, C)
    rhs = tm.mkTerm(Kind.SET_UNION, intersectionAC, intersectionBC)

    theorem = tm.mkTerm(Kind.EQUAL, lhs, rhs)

    print("cvc5 reports: {} is {}".format(
        theorem.notTerm(), slv.checkSatAssuming(theorem.notTerm())))

    # Verify emptset is a subset of any set

    A = tm.mkConst(set_, "A")
    emptyset = tm.mkEmptySet(set_)

    theorem = tm.mkTerm(Kind.SET_SUBSET, emptyset, A)

    print("cvc5 reports: {} is {}".format(
        theorem.notTerm(), slv.checkSatAssuming(theorem.notTerm())))

    # Find me an element in 1, 2 intersection 2, 3, if there is one.

    one = tm.mkInteger(1)
    two = tm.mkInteger(2)
    three = tm.mkInteger(3)

    singleton_one = tm.mkTerm(Kind.SET_SINGLETON, one)
    singleton_two = tm.mkTerm(Kind.SET_SINGLETON, two)
    singleton_three = tm.mkTerm(Kind.SET_SINGLETON, three)
    one_two = tm.mkTerm(Kind.SET_UNION, singleton_one, singleton_two)
    two_three = tm.mkTerm(Kind.SET_UNION, singleton_two, singleton_three)
    intersection = tm.mkTerm(Kind.SET_INTER, one_two, two_three)

    x = tm.mkConst(integer, "x")

    e = tm.mkTerm(Kind.SET_MEMBER, x, intersection)

    result = slv.checkSatAssuming(e)

    print("cvc5 reports: {} is {}".format(e, result))

    if result:
        print("For instance, {} is a member".format(slv.getValue(x)))
