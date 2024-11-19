###############################################################################
# Top contributors (to current version):
#   Andrew Reynolds, Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple test of multiple SmtEngines.
##

import cvc5

tm = cvc5.TermManager()
s1 = cvc5.Solver(tm)
s2 = cvc5.Solver(tm)
r1 = s1.checkSatAssuming(tm.mkBoolean(False))
r2 = s2.checkSatAssuming(tm.mkBoolean(False))
assert r1.isUnsat() and r2.isUnsat()
