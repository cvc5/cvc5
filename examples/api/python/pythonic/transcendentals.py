###############################################################################
# Top contributors (to current version):
#   Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple demonstration of the transcendental extension.
##
from cvc5.pythonic import *

if __name__ == '__main__':
    x, y = Reals("x y")
    solve(x > Pi(),
            x < 2 * Pi(),
            y ** 2 < Sine(x))
