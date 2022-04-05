#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Makai Mann, Aina Niemetz, Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple demonstration of the solving capabilities of the cvc5 strings solver
# through the Python API. This is a direct translation of strings-new.cpp.
##

import cvc5
from cvc5 import Kind

if __name__ == "__main__":
    slv = cvc5.Solver()
    # Set the logic
    slv.setLogic("QF_SLIA")
    # Produce models
    slv.setOption("produce-models", "true")
    # The option strings-exp is needed
    slv.setOption("strings-exp", "true")
    # Set output language to SMTLIB2
    slv.setOption("output-language", "smt2")

    # String type
    string = slv.getStringSort()

    # std::string
    str_ab = "ab"
    # String constants
    ab  = slv.mkString(str_ab)
    abc = slv.mkString("abc")
    # String variables
    x = slv.mkConst(string, "x")
    y = slv.mkConst(string, "y")
    z = slv.mkConst(string, "z")

    # String concatenation: x.ab.y
    lhs = slv.mkTerm(Kind.STRING_CONCAT, x, ab, y)
    # String concatenation: abc.z
    rhs = slv.mkTerm(Kind.STRING_CONCAT, abc, z)
    # x.ab.y = abc.z
    formula1 = slv.mkTerm(Kind.EQUAL, lhs, rhs)

    # Length of y: |y|
    leny = slv.mkTerm(Kind.STRING_LENGTH, y)
    # |y| >= 0
    formula2 = slv.mkTerm(Kind.GEQ, leny, slv.mkInteger(0))

    # Regular expression: (ab[c-e]*f)|g|h
    r = slv.mkTerm(Kind.REGEXP_UNION,
                   slv.mkTerm(Kind.REGEXP_CONCAT,
                              slv.mkTerm(Kind.STRING_TO_REGEXP,
                                         slv.mkString("ab")),
                              slv.mkTerm(Kind.REGEXP_STAR,
                                         slv.mkTerm(Kind.REGEXP_RANGE,
                                         slv.mkString("c"),
                                         slv.mkString("e"))),
                            slv.mkTerm(Kind.STRING_TO_REGEXP,
                                       slv.mkString("f"))),
                 slv.mkTerm(Kind.STRING_TO_REGEXP, slv.mkString("g")),
                 slv.mkTerm(Kind.STRING_TO_REGEXP, slv.mkString("h")))

    # String variables
    s1 = slv.mkConst(string, "s1")
    s2 = slv.mkConst(string, "s2")
    # String concatenation: s1.s2
    s = slv.mkTerm(Kind.STRING_CONCAT, s1, s2)

    # s1.s2 in (ab[c-e]*f)|g|h
    formula3 = slv.mkTerm(Kind.STRING_IN_REGEXP, s, r)

    # Make a query
    q = slv.mkTerm(Kind.AND,
                   formula1,
                   formula2,
                   formula3)

    # check sat
    result = slv.checkSatAssuming(q)
    print("cvc5 reports:", q, "is", result)

    if result:
        print("x = ", slv.getValue(x))
        print(" s1.s2 =", slv.getValue(s))
