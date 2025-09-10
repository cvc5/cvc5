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
# A simple demonstration of the solving capabilities of the cvc5
# bit-vector solver.
##
from cvc5.pythonic import *

if __name__ == '__main__':
    x = BitVec('x', 32)

    # Consider the bits of x: 01234567
    # (we assume 8 bits to make the visualization simple)
    #
    # If      1234567
    # equals  0123456
    #
    # then    0 == 7 (by induction over the bits)

    prove(Implies(Extract(31, 1, x) == Extract(30, 0, x),
                  Extract(31, 31, x) == Extract(0, 0, x)))
