###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Aina Niemetz, Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Test for issue #6111
##

import cvc5
from cvc5 import Kind

tm = cvc5.TermManager()
solver = cvc5.Solver(tm)
solver.setLogic("QF_BV")
bvsort12979 = tm.mkBitVectorSort(12979)
input2_1 = tm.mkConst(bvsort12979, "intpu2_1")
zero = tm.mkBitVector(bvsort12979.getBitVectorSize(), "0", 10)

bvult_res = tm.mkTerm(Kind.BITVECTOR_ULT, zero, input2_1)
solver.assertFormula(bvult_res)

bvsort4 = tm.mkBitVectorSort(4)
concat_result_42 = tm.mkConst(bvsort4, "concat_result_42")
bvsort8 = tm.mkBitVectorSort(8)
concat_result_43 = tm.mkConst(bvsort8, "concat_result_43")

args2 = []
args2.append(concat_result_42)
args2.append(tm.mkTerm(tm.mkOp(Kind.BITVECTOR_EXTRACT, 7, 4), concat_result_43))
solver.assertFormula(tm.mkTerm(Kind.EQUAL, *args2))

args3 = []
args3.append(concat_result_42)
args3.append(tm.mkTerm(tm.mkOp(Kind.BITVECTOR_EXTRACT, 3, 0), concat_result_43))
solver.assertFormula(tm.mkTerm(Kind.EQUAL, *args3))

print(solver.checkSat())
