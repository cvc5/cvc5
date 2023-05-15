###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Andrew Reynolds, Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

slv = cvc5.Solver()
slv.setOption("incremental", "true")

real = slv.getRealSort()
x = slv.mkConst(real, "x")
four = slv.mkReal(4)
xEqFour = slv.mkTerm(Kind.EQUAL, x, four)
slv.assertFormula(xEqFour)
print(slv.checkSat())

slv.resetAssertions()

elementType = slv.getIntegerSort()
indexType = slv.getIntegerSort()
arrayType = slv.mkArraySort(indexType, elementType)
array = slv.mkConst(arrayType, "array")
fourInt = slv.mkInteger(4)
arrayAtFour = slv.mkTerm(Kind.SELECT, array, fourInt)
ten = slv.mkInteger(10)
arrayAtFour_eq_ten = slv.mkTerm(Kind.EQUAL, arrayAtFour, ten)
slv.assertFormula(arrayAtFour_eq_ten)
print(slv.checkSat())
