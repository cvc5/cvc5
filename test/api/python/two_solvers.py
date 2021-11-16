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

import pycvc5

s1 = pycvc5.Solver()
s2 = pycvc5.Solver()
r = s1.checkEntailed(s1.mkBoolean(True))
r2 = s2.checkEntailed(s2.mkBoolean(True))
print(0 if r.isEntailed() and r2.isEntailed() else 1)
