###############################################################################
# Top contributors (to current version):
#   Yoni Zohar
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple demonstration of the capabilities of the cvc5 uf solver.
##
from cvc5.pythonic import *

if __name__ == "__main__":

    U = DeclareSort("U")
    x, y = Consts("x y", U)

    f = Function("f", U, U)
    p = Function("p", U, BoolSort())

    assumptions = [f(x) == x, f(y) == y, Not(p(f(x))), p(f(y))]

    s = Solver()
    s.add(assumptions)
    assert sat == s.check()
