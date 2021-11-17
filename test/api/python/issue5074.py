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

import pycvc5
from pycvc5 import kinds

slv = pycvc5.Solver()
c1 = slv.mkConst(slv.getIntegerSort())
t6 = slv.mkTerm(kinds.StringFromCode, c1)
t12 = slv.mkTerm(kinds.StringToRegexp, t6)
t14 = slv.mkTerm(kinds.StringReplaceRe, [t6, t12, t6])
t16 = slv.mkTerm(kinds.StringContains, [t14, t14])
slv.checkEntailed(t16)
