#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Andres Noetzli
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Catching cvc5 exceptions with the legacy Python API.
#
# A simple demonstration of catching cvc5 exceptions with the legacy Python API.
##

import pycvc5
from pycvc5 import kinds
import sys


def main():
    slv = pycvc5.Solver()

    slv.setOption("produce-models", "true")

    # Setting an invalid option
    try:
        slv.setOption("non-existing", "true")
        return 1
    except:
        pass

    # Creating a term with an invalid type
    try:
        integer = slv.getIntegerSort()
        x = slv.mkConst("x", integer)
        invalidTerm = em.mkTerm(AND, x, x)
        slv.checkSat(invalidTerm)
        return 1
    except:
        pass

    # Asking for a model after unsat result
    try:
        slv.checkSat(slv.mkBoolean(False))
        slv.getModel()
        return 1
    except:
        pass

    return 0


if __name__ == '__main__':
    sys.exit(main())
