###############################################################################
# Top contributors (to current version):
#   Aina Niemetz, Alex Ozdemir, Yoni Zohar
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Test for issue #5074
##

import cvc5
from cvc5 import Kind

slv = cvc5.Solver()
c1 = slv.mkConst(slv.getIntegerSort())
t6 = slv.mkTerm(Kind.STRING_FROM_CODE, c1)
t12 = slv.mkTerm(Kind.STRING_TO_REGEXP, t6)
t14 = slv.mkTerm(Kind.STRING_REPLACE_RE, t6, t12, t6)
t16 = slv.mkTerm(Kind.STRING_CONTAINS, t14, t14)
slv.checkSatAssuming(t16.notTerm())
