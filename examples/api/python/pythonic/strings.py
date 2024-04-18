#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Yoni Zohar
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# ############################################################################
#
# A simple demonstration of the solving capabilities of the cvc5 strings solver. A simple translation of the base python API
# example.
##

from cvc5.pythonic import *

if __name__ == "__main__":

    str_ab = "ab"
    # String constants
    ab  = StringVal(str_ab)
    abc = StringVal("abc")
    # String variables
    x = String("x")
    y = String("y")
    z = String("z")

    # String concatenation: x.ab.y
    lhs = Concat(x, ab, y)
    # String concatenation: abc.z
    rhs = Concat(abc, z)
    # x.ab.y = abc.z
    formula1 = (lhs == rhs)

    # Length of y: |y|
    leny = Length(y)
    # |y| >= 0
    formula2 = leny >= 0

    # Regular expression: (ab[c-e]*f)|g|h
    r = Union(Concat(Re("ab"), Star(Range("c", "e")), Re("f")), Re("g"), Re("h"))


    # String variables
    s1 = String("s1")
    s2 = String("s2")
    # String concatenation: s1.s2
    s = Concat(s1, s2)

    # s1.s2 in (ab[c-e]*f)|g|h
    formula3 = InRe(s,r)

    # Make a query
    q = And(formula1, formula2, formula3)

    # check sat
    s = Solver()
    s.add(q)
    assert sat == s.check()
    m = s.model()
    print("x = ", m[x])
    print(" s1.s2 =", m[Concat(s1, s2)])
