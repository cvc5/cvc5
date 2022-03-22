##############################################################################
# Top contributors (to current version):
#   Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# ############################################################################
#
# Operator indices
##

import cvc5
from cvc5 import Kind

slv = cvc5.Solver()
o = slv.mkOp(Kind.BVExtract, 6, 2)
assert o.getNumIndices() == 2
assert o[0].toPythonObj() == 6
assert o[1].toPythonObj() == 2
