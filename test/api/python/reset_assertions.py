###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Andrew Reynolds, Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple test for SolverEngine::resetAssertions()
#
# This program indirectly also tests some corner cases w.r.t.
# context-dependent datastructures: resetAssertions() pops the contexts to
# zero but some context-dependent datastructures are created at leevel 1,
# which the datastructure needs to handle properly problematic.
##

import cvc5
from cvc5 import Kind

tm = cvc5.TermManager()
slv = cvc5.Solver(tm)
slv.setOption("incremental", "true")

real = tm.getRealSort()
x = tm.mkConst(real, "x")
four = tm.mkReal(4)
xEqFour = tm.mkTerm(Kind.EQUAL, x, four)
slv.assertFormula(xEqFour)
print(slv.checkSat())

slv.resetAssertions()

elementType = tm.getIntegerSort()
indexType = tm.getIntegerSort()
arrayType = tm.mkArraySort(indexType, elementType)
array = tm.mkConst(arrayType, "array")
fourInt = tm.mkInteger(4)
arrayAtFour = tm.mkTerm(Kind.SELECT, array, fourInt)
ten = tm.mkInteger(10)
arrayAtFour_eq_ten = tm.mkTerm(Kind.EQUAL, arrayAtFour, ten)
slv.assertFormula(arrayAtFour_eq_ten)
print(slv.checkSat())
