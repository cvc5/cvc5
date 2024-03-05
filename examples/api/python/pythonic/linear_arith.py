###############################################################################
# Top contributors (to current version):
#   Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
from cvc5.pythonic import *

slv = SolverFor('QF_LIRA')

x = Int('x')
y = Real('y')

slv += And(x >= 3 * y, x <= y, -2 < x)
slv.push()
print(slv.check(y-x <= 2/3))
slv.pop()
slv.push()
slv += y-x == 2/3
print(slv.check())
slv.pop()
