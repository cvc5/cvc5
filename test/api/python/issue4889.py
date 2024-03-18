###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Alex Ozdemir, Aina Niemetz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Test for issue #4889
##

import cvc5
from cvc5 import Kind

tm = cvc5.TermManager()
slv = cvc5.Solver(tm)
sort_int = tm.getIntegerSort()
sort_array = tm.mkArraySort(sort_int, sort_int)
sort_fp128 = tm.mkFloatingPointSort(15, 113)
sort_fp32 = tm.mkFloatingPointSort(8, 24)
sort_bool = tm.getBooleanSort()
const0 = tm.mkConst(sort_fp32, "_c0")
const1 = tm.mkConst(sort_fp32, "_c2")
const2 = tm.mkConst(sort_bool, "_c4")
ite = tm.mkTerm(Kind.ITE, const2, const1, const0)
rem = tm.mkTerm(Kind.FLOATINGPOINT_REM, ite, const1)
isnan = tm.mkTerm(Kind.FLOATINGPOINT_IS_NAN, rem)
slv.checkSatAssuming(isnan)
