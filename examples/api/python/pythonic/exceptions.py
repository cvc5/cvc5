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
# A simple demonstration of how to handle exceptions.
##
from cvc5.pythonic import *

if __name__ == '__main__':
    s = Solver()
    s.set("produce-models", True)
    try:
        # invalid option
        s.set("non-existing-option", True)
    except:
        pass

    try:
        # type error
        Int("x") + BitVec("a", 5)
    except:
        pass

    s += BoolVal(False)
    s.check()
    try:
        s.model()
    except:
        pass
