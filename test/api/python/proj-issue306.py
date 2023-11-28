###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Alex Ozdemir, Aina Niemetz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
##

import cvc5
from cvc5 import Kind

slv = cvc5.Solver()
slv.setOption("check-proofs", "true")
slv.setOption("proof-check", "eager")
s1 = slv.getBooleanSort()
s3 = slv.getStringSort()
t1 = slv.mkConst(s3, "_x0")
t3 = slv.mkConst(s1, "_x2")
t11 = slv.mkString("")
t14 = slv.mkConst(s3, "_x11")
t42 = slv.mkTerm(Kind.ITE, t3, t14, t1)
t58 = slv.mkTerm(Kind.STRING_LEQ, t14, t11)
t95 = slv.mkTerm(Kind.EQUAL, t14, t42)
slv.assertFormula(t95)
slv.checkSatAssuming(t58)
