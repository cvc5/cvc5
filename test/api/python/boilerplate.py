###############################################################################
# Top contributors (to current version):
#   Andrew Reynolds, Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# [[ Add one-line brief description here ]]
#
# [[ Add lengthier description here ]]
# \todo document this file
##
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
# A simple start-up/tear-down test for cvc5.
#
# This simple test just makes sure that the public interface is
# minimally functional.  It is useful as a template to use for other
# system tests.
##

import cvc5

slv = cvc5.Solver()
r = slv.checkSatAssuming(slv.mkBoolean(False))
r.isUnsat()
