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
# An example of solving finite field problems with cvc5's Python API.
##
from cvc5.pythonic import *

if __name__ == '__main__':
    F = FiniteFieldSort(5)
    a, b = FiniteFieldElems("a b", F)
    s = Solver()

    # a = 2, b = -2 (or 3) is a solution.
    r = s.check(a * b == 1, a == 2)
    assert r == sat
    print(s.model()[a])
    assert s.model()[b] == -2

    # no solution
    r = s.check(a * b == 1, a == 2, b == 2)
    assert r == unsat
