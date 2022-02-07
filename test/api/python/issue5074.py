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
# Test for issue #5074
##

import cvc5
from cvc5 import Kind

slv = cvc5.Solver()
c1 = slv.mkConst(slv.getIntegerSort())
t6 = slv.mkTerm(Kind.StringFromCode, c1)
t12 = slv.mkTerm(Kind.StringToRegexp, t6)
t14 = slv.mkTerm(Kind.StringReplaceRe, [t6, t12, t6])
t16 = slv.mkTerm(Kind.StringContains, [t14, t14])
slv.checkEntailed(t16)
