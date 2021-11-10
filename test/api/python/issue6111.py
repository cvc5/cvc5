##############################################################################
# Top contributors (to current version):
#   Yoni Zohar
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# ############################################################################
#
# Test for issue #6111
##

import pycvc5
from pycvc5 import kinds

solver = pycvc5.Solver()
solver.setLogic("QF_BV")
bvsort12979 = solver.mkBitVectorSort(12979)
input2_1 = solver.mkConst(bvsort12979, "intpu2_1")
zero = solver.mkBitVector(bvsort12979.getBitVectorSize(), "0", 10)

args1 = []
args1.append(zero)
args1.append(input2_1)
bvult_res = solver.mkTerm(kinds.BVUlt, args1)
solver.assertFormula(bvult_res)

bvsort4 = solver.mkBitVectorSort(4)
concat_result_42 = solver.mkConst(bvsort4, "concat_result_42")
bvsort8 = solver.mkBitVectorSort(8)
concat_result_43 = solver.mkConst(bvsort8, "concat_result_43")

args2 = []
args2.append(concat_result_42)
args2.append(
    solver.mkTerm(solver.mkOp(kinds.BVExtract, 7, 4), [concat_result_43]))
solver.assertFormula(solver.mkTerm(kinds.Equal, args2))

args3 = []
args3.append(concat_result_42)
args3.append(
    solver.mkTerm(solver.mkOp(kinds.BVExtract, 3, 0), [concat_result_43]))
solver.assertFormula(solver.mkTerm(kinds.Equal, args3))

print(solver.checkSat())
