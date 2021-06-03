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
# A simple demonstration of the solving capabilities of the cvc5 sets solver
# through the Python API. This is a direct translation of sets-new.cpp.
##

import pycvc5
from pycvc5 import kinds

if __name__ == "__main__":
    slv = pycvc5.Solver()

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

    unionAB = slv.mkTerm(kinds.Union, A, B)
    lhs = slv.mkTerm(kinds.Intersection, unionAB, C)

    intersectionAC = slv.mkTerm(kinds.Intersection, A, C)
    intersectionBC = slv.mkTerm(kinds.Intersection, B, C)
    rhs = slv.mkTerm(kinds.Union, intersectionAC, intersectionBC)

    theorem = slv.mkTerm(kinds.Equal, lhs, rhs)

    print("cvc5 reports: {} is {}".format(theorem,
                                          slv.checkEntailed(theorem)))

    # Verify emptset is a subset of any set

    A = slv.mkConst(set_, "A")
    emptyset = slv.mkEmptySet(set_)

    theorem = slv.mkTerm(kinds.Subset, emptyset, A)

    print("cvc5 reports: {} is {}".format(theorem,
                                          slv.checkEntailed(theorem)))

    # Find me an element in 1, 2 intersection 2, 3, if there is one.

    one = slv.mkInteger(1)
    two = slv.mkInteger(2)
    three = slv.mkInteger(3)

    singleton_one = slv.mkTerm(kinds.Singleton, one)
    singleton_two = slv.mkTerm(kinds.Singleton, two)
    singleton_three = slv.mkTerm(kinds.Singleton, three)
    one_two = slv.mkTerm(kinds.Union, singleton_one, singleton_two)
    two_three = slv.mkTerm(kinds.Union, singleton_two, singleton_three)
    intersection = slv.mkTerm(kinds.Intersection, one_two, two_three)

    x = slv.mkConst(integer, "x")

    e = slv.mkTerm(kinds.Member, x, intersection)

    result = slv.checkSatAssuming(e)

    print("cvc5 reports: {} is {}".format(e, result))

    if result:
        print("For instance, {} is a member".format(slv.getValue(x)))
