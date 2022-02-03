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
# A simple test of multiple SmtEngines.
##

import cvc5

s1 = cvc5.Solver()
s2 = cvc5.Solver()
r1 = s1.checkEntailed(s1.mkBoolean(True))
r2 = s2.checkEntailed(s2.mkBoolean(True))
assert r1.isEntailed() and r2.isEntailed()
