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
# Test for issue #4889
##

import pycvc5
from pycvc5 import Kind

slv = pycvc5.Solver()
sort_int = slv.getIntegerSort()
sort_array = slv.mkArraySort(sort_int, sort_int)
sort_fp128 = slv.mkFloatingPointSort(15, 113)
sort_fp32 = slv.mkFloatingPointSort(8, 24)
sort_bool = slv.getBooleanSort()
const0 = slv.mkConst(sort_fp32, "_c0")
const1 = slv.mkConst(sort_fp32, "_c2")
const2 = slv.mkConst(sort_bool, "_c4")
ite = slv.mkTerm(Kind.Ite, const2, const1, const0)
rem = slv.mkTerm(Kind.FPRem, ite, const1)
isnan = slv.mkTerm(Kind.FPIsNan, rem)
slv.checkSatAssuming(isnan)
