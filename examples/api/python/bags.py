#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Mudathir Mohamed
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple demonstration of reasoning about bags.
##

import cvc5
from cvc5 import Kind

if __name__ == "__main__":
    slv = cvc5.Solver()
    slv.setLogic("ALL")

    # Produce models
    slv.setOption("produce-models", "true")
    slv.setOption("incremental", "true")

    bag = slv.mkBagSort(slv.getStringSort())
    A = slv.mkConst(bag, "A")
    B = slv.mkConst(bag, "B")
    C = slv.mkConst(bag, "C")
    x = slv.mkConst(slv.getStringSort(), "x")

    intersectionAC = slv.mkTerm(Kind.BagInterMin, A, C)
    intersectionBC = slv.mkTerm(Kind.BagInterMin, B, C)

    # union disjoint does not distribute over intersection
    unionDisjointAB = slv.mkTerm(Kind.BagUnionDisjoint, A, B)
    lhs = slv.mkTerm(Kind.BagInterMin, unionDisjointAB, C)
    rhs = slv.mkTerm(Kind.BagUnionDisjoint, intersectionAC, intersectionBC)
    guess = slv.mkTerm(Kind.Equal, lhs, rhs)
    print("cvc5 reports: {} is {}".format(guess.notTerm(), slv.checkSatAssuming(guess.notTerm())))

    print("{}: {}".format(A, slv.getValue(A)))
    print("{}: {}".format(B, slv.getValue(B)))
    print("{}: {}".format(C, slv.getValue(C)))
    print("{}: {}".format(lhs, slv.getValue(lhs)))
    print("{}: {}".format(rhs, slv.getValue(rhs)))

    # union max distributes over intersection
    unionMaxAB = slv.mkTerm(Kind.BagUnionMax, A, B)
    lhs = slv.mkTerm(Kind.BagInterMin, unionMaxAB, C)
    rhs = slv.mkTerm(Kind.BagUnionMax, intersectionAC, intersectionBC)
    theorem = slv.mkTerm(Kind.Equal, lhs, rhs)
    print("cvc5 reports: {} is {}.".format(theorem.notTerm(), slv.checkSatAssuming(theorem.notTerm())))

    # Verify emptbag is a subbag of any bag
    emptybag = slv.mkEmptyBag(bag)
    theorem = slv.mkTerm(Kind.BagSubbag, emptybag, A)
    print("cvc5 reports: {} is {}.".format(theorem.notTerm(), slv.checkSatAssuming(theorem.notTerm())))

    # find an element with multiplicity 4 in the disjoint union of
    #  {|"a", "a", "b", "b", "b"|} and {|"b", "c", "c"|}
    one = slv.mkInteger(1)
    two = slv.mkInteger(2)
    three = slv.mkInteger(3)
    four = slv.mkInteger(4)
    a = slv.mkString("a")
    b = slv.mkString("b")
    c = slv.mkString("c")

    bag_a_2 = slv.mkTerm(Kind.BagMake, a, two)
    bag_b_3 = slv.mkTerm(Kind.BagMake, b, three)
    bag_b_1 = slv.mkTerm(Kind.BagMake, b, one)
    bag_c_2 = slv.mkTerm(Kind.BagMake, c, two)
    bag_a_2_b_3 = slv.mkTerm(Kind.BagUnionDisjoint, bag_a_2, bag_b_3)
    bag_b_1_c_2 = slv.mkTerm(Kind.BagUnionDisjoint, bag_b_1, bag_c_2)
    UnionDisjoint = slv.mkTerm(Kind.BagUnionDisjoint, bag_a_2_b_3, bag_b_1_c_2)

    count_x = slv.mkTerm(Kind.BagCount, x, UnionDisjoint)
    e = slv.mkTerm(Kind.Equal, four, count_x)
    result = slv.checkSatAssuming(e)

    print("cvc5 reports: {} is {}.".format(e, result))
    if result.isSat():
        print("{}: {} ".format(x, slv.getValue(x)))
