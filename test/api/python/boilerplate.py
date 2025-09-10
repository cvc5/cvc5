###############################################################################
# Top contributors (to current version):
#   Aina Niemetz, Andrew Reynolds, Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple start-up/tear-down test for cvc5.
#
# This simple test just makes sure that the public interface is
# minimally functional.  It is useful as a template to use for other
# system tests.
##

import cvc5

tm = cvc5.TermManager()
slv = cvc5.Solver(tm)
r = slv.checkSatAssuming(tm.mkBoolean(False))
r.isUnsat()
