###############################################################################
# Top contributors (to current version):
#   Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple start-up/tear-down test for cvc5.
#
# This simple test just makes sure that the public interface is
# minimally functional.  It is useful as a template to use for other
# system tests.
##

import cvc5
from cvc5 import Kind

slv = cvc5.Solver()
slv.setOption("produce-models", "true")
F = slv.mkFiniteFieldSort(5)
a = slv.mkConst(F, "a")
b = slv.mkConst(F, "b")
assert 5 == F.getFiniteFieldSize()

inv = slv.mkTerm(
    Kind.EQUAL,
    slv.mkTerm(Kind.FINITE_FIELD_MULT, a, b),
    slv.mkFiniteFieldElem(1, F),
)
aIsTwo = slv.mkTerm(
    Kind.EQUAL,
    a,
    slv.mkFiniteFieldElem(2, F),
)
slv.assertFormula(inv)
slv.assertFormula(aIsTwo)
r = slv.checkSat()
assert r.isSat()
assert slv.getValue(a).toPythonObj() == 2
assert slv.getValue(b).toPythonObj() == -2

bIsTwo = slv.mkTerm(
    Kind.EQUAL,
    b,
    slv.mkFiniteFieldElem(2, F),
)
slv.assertFormula(bIsTwo)
r = slv.checkSat()
assert not r.isSat()
