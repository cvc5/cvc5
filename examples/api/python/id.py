#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple demonstration of the solving capabilities of the cvc5 sets solver
# through the Python API. This is a direct translation of sets-new.cpp.
##

import pycvc5
from pycvc5 import kinds

if __name__ == "__main__":
    slv = pycvc5.Solver()

    # Optionally, set the logic. We need at least UF for equality predicate,
    # integers (LIA) and sets (FS).
    slv.setLogic("QF_UFLIAFS")

    integer = slv.getIntegerSort()
    set_ = slv.mkSetSort(integer)

    A = slv.mkConst(set_, "A")
    B = slv.mkConst(set_, "B")
    C = slv.mkConst(set_, "C")

    assert A.getId() != B.getId()
    assert C.getId() != B.getId()
    assert A.getId() == A.getId()
    assert B.getId() == B.getId()
    assert C.getId() == C.getId()
