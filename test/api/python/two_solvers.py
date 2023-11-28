###############################################################################
# Top contributors (to current version):
#   Andrew Reynolds, Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple test of multiple SmtEngines.
##

import cvc5

s1 = cvc5.Solver()
s2 = cvc5.Solver()
r1 = s1.checkSatAssuming(s1.mkBoolean(False))
r2 = s2.checkSatAssuming(s2.mkBoolean(False))
assert r1.isUnsat() and r2.isUnsat()
