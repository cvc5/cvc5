#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Aina Niemetz, Mudathir Mohamed
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
    tm = cvc5.TermManager()
    slv = cvc5.Solver(tm)
    slv.setLogic("ALL")

    # Produce models
    slv.setOption("produce-models", "true")
    slv.setOption("incremental", "true")

    bag = tm.mkBagSort(tm.getStringSort())
    A = tm.mkConst(bag, "A")
    B = tm.mkConst(bag, "B")
    C = tm.mkConst(bag, "C")
    x = tm.mkConst(tm.getStringSort(), "x")

    intersectionAC = tm.mkTerm(Kind.BAG_INTER_MIN, A, C)
    intersectionBC = tm.mkTerm(Kind.BAG_INTER_MIN, B, C)

    # union disjoint does not distribute over intersection
    unionDisjointAB = tm.mkTerm(Kind.BAG_UNION_DISJOINT, A, B)
    lhs = tm.mkTerm(Kind.BAG_INTER_MIN, unionDisjointAB, C)
    rhs = tm.mkTerm(Kind.BAG_UNION_DISJOINT, intersectionAC, intersectionBC)
    guess = tm.mkTerm(Kind.EQUAL, lhs, rhs)
    print("cvc5 reports: {} is {}".format(
        guess.notTerm(), slv.checkSatAssuming(guess.notTerm())))

    print("{}: {}".format(A, slv.getValue(A)))
    print("{}: {}".format(B, slv.getValue(B)))
    print("{}: {}".format(C, slv.getValue(C)))
    print("{}: {}".format(lhs, slv.getValue(lhs)))
    print("{}: {}".format(rhs, slv.getValue(rhs)))

    # union max distributes over intersection
    unionMaxAB = tm.mkTerm(Kind.BAG_UNION_MAX, A, B)
    lhs = tm.mkTerm(Kind.BAG_INTER_MIN, unionMaxAB, C)
    rhs = tm.mkTerm(Kind.BAG_UNION_MAX, intersectionAC, intersectionBC)
    theorem = tm.mkTerm(Kind.EQUAL, lhs, rhs)
    print("cvc5 reports: {} is {}.".format(
        theorem.notTerm(), slv.checkSatAssuming(theorem.notTerm())))

    # Verify emptbag is a subbag of any bag
    emptybag = tm.mkEmptyBag(bag)
    theorem = tm.mkTerm(Kind.BAG_SUBBAG, emptybag, A)
    print("cvc5 reports: {} is {}.".format(
        theorem.notTerm(), slv.checkSatAssuming(theorem.notTerm())))

    # find an element with multiplicity 4 in the disjoint union of
    #  {|"a", "a", "b", "b", "b"|} and {|"b", "c", "c"|}
    one = tm.mkInteger(1)
    two = tm.mkInteger(2)
    three = tm.mkInteger(3)
    four = tm.mkInteger(4)
    a = tm.mkString("a")
    b = tm.mkString("b")
    c = tm.mkString("c")

    bag_a_2 = tm.mkTerm(Kind.BAG_MAKE, a, two)
    bag_b_3 = tm.mkTerm(Kind.BAG_MAKE, b, three)
    bag_b_1 = tm.mkTerm(Kind.BAG_MAKE, b, one)
    bag_c_2 = tm.mkTerm(Kind.BAG_MAKE, c, two)
    bag_a_2_b_3 = tm.mkTerm(Kind.BAG_UNION_DISJOINT, bag_a_2, bag_b_3)
    bag_b_1_c_2 = tm.mkTerm(Kind.BAG_UNION_DISJOINT, bag_b_1, bag_c_2)
    UnionDisjoint = tm.mkTerm(
            Kind.BAG_UNION_DISJOINT, bag_a_2_b_3, bag_b_1_c_2)

    count_x = tm.mkTerm(Kind.BAG_COUNT, x, UnionDisjoint)
    e = tm.mkTerm(Kind.EQUAL, four, count_x)
    result = slv.checkSatAssuming(e)

    print("cvc5 reports: {} is {}.".format(e, result))
    if result.isSat():
        print("{}: {} ".format(x, slv.getValue(x)))
