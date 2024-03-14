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
# A simple demonstration of the solving capabilities of the cvc5 strings solver
# through the Python API. This is a direct translation of strings-new.cpp.
##

import cvc5
from cvc5 import Kind

if __name__ == "__main__":
    tm = cvc5.TermManager()
    slv = cvc5.Solver(tm)
    # Set the logic
    slv.setLogic("QF_SLIA")
    # Produce models
    slv.setOption("produce-models", "true")
    # The option strings-exp is needed
    slv.setOption("strings-exp", "true")
    # Set output language to SMTLIB2
    slv.setOption("output-language", "smt2")

    # String type
    string = tm.getStringSort()

    # std::string
    str_ab = "ab"
    # String constants
    ab  = tm.mkString(str_ab)
    abc = tm.mkString("abc")
    # String variables
    x = tm.mkConst(string, "x")
    y = tm.mkConst(string, "y")
    z = tm.mkConst(string, "z")

    # String concatenation: x.ab.y
    lhs = tm.mkTerm(Kind.STRING_CONCAT, x, ab, y)
    # String concatenation: abc.z
    rhs = tm.mkTerm(Kind.STRING_CONCAT, abc, z)
    # x.ab.y = abc.z
    formula1 = tm.mkTerm(Kind.EQUAL, lhs, rhs)

    # Length of y: |y|
    leny = tm.mkTerm(Kind.STRING_LENGTH, y)
    # |y| >= 0
    formula2 = tm.mkTerm(Kind.GEQ, leny, tm.mkInteger(0))

    # Regular expression: (ab[c-e]*f)|g|h
    r = tm.mkTerm(Kind.REGEXP_UNION,
                   tm.mkTerm(Kind.REGEXP_CONCAT,
                              tm.mkTerm(Kind.STRING_TO_REGEXP,
                                         tm.mkString("ab")),
                              tm.mkTerm(Kind.REGEXP_STAR,
                                         tm.mkTerm(Kind.REGEXP_RANGE,
                                         tm.mkString("c"),
                                         tm.mkString("e"))),
                            tm.mkTerm(Kind.STRING_TO_REGEXP,
                                       tm.mkString("f"))),
                 tm.mkTerm(Kind.STRING_TO_REGEXP, tm.mkString("g")),
                 tm.mkTerm(Kind.STRING_TO_REGEXP, tm.mkString("h")))

    # String variables
    s1 = tm.mkConst(string, "s1")
    s2 = tm.mkConst(string, "s2")
    # String concatenation: s1.s2
    s = tm.mkTerm(Kind.STRING_CONCAT, s1, s2)

    # s1.s2 in (ab[c-e]*f)|g|h
    formula3 = tm.mkTerm(Kind.STRING_IN_REGEXP, s, r)

    # Make a query
    q = tm.mkTerm(Kind.AND, formula1, formula2, formula3)

    # check sat
    result = slv.checkSatAssuming(q)
    print("cvc5 reports:", q, "is", result)

    if result:
        print("x = ", slv.getValue(x))
        print(" s1.s2 =", slv.getValue(s))
