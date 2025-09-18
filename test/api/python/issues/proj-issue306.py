###############################################################################
# Top contributors (to current version):
#   Aina Niemetz, Yoni Zohar, Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
##

import cvc5
from cvc5 import Kind

tm = cvc5.TermManager()
slv = cvc5.Solver(tm)
slv.setOption("check-proofs", "true")
slv.setOption("proof-check", "eager")
s1 = tm.getBooleanSort()
s3 = tm.getStringSort()
t1 = tm.mkConst(s3, "_x0")
t3 = tm.mkConst(s1, "_x2")
t11 = tm.mkString("")
t14 = tm.mkConst(s3, "_x11")
t42 = tm.mkTerm(Kind.ITE, t3, t14, t1)
t58 = tm.mkTerm(Kind.STRING_LEQ, t14, t11)
t95 = tm.mkTerm(Kind.EQUAL, t14, t42)
slv.assertFormula(t95)
slv.checkSatAssuming(t58)
