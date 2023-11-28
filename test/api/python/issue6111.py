###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Aina Niemetz, Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Test for issue #6111
##

import cvc5
from cvc5 import Kind

solver = cvc5.Solver()
solver.setLogic("QF_BV")
bvsort12979 = solver.mkBitVectorSort(12979)
input2_1 = solver.mkConst(bvsort12979, "intpu2_1")
zero = solver.mkBitVector(bvsort12979.getBitVectorSize(), "0", 10)

bvult_res = solver.mkTerm(Kind.BITVECTOR_ULT, zero, input2_1)
solver.assertFormula(bvult_res)

bvsort4 = solver.mkBitVectorSort(4)
concat_result_42 = solver.mkConst(bvsort4, "concat_result_42")
bvsort8 = solver.mkBitVectorSort(8)
concat_result_43 = solver.mkConst(bvsort8, "concat_result_43")

args2 = []
args2.append(concat_result_42)
args2.append(
    solver.mkTerm(solver.mkOp(Kind.BITVECTOR_EXTRACT, 7, 4), concat_result_43))
solver.assertFormula(solver.mkTerm(Kind.EQUAL, *args2))

args3 = []
args3.append(concat_result_42)
args3.append(
    solver.mkTerm(solver.mkOp(Kind.BITVECTOR_EXTRACT, 3, 0), concat_result_43))
solver.assertFormula(solver.mkTerm(Kind.EQUAL, *args3))

print(solver.checkSat())
