#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Alex Ozdemir, Aina Niemetz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple demonstration of the getId function exposed by the cvc5 terms python
# API
##

import cvc5

if __name__ == "__main__":
    tm = cvc5.TermManager()
    slv = cvc5.Solver(tm)

    integer = tm.getIntegerSort()
    set_ = tm.mkSetSort(integer)

    A = tm.mkConst(set_, "A")
    B = tm.mkConst(set_, "B")
    C = tm.mkConst(set_, "C")

    assert A.getId() != B.getId()
    assert C.getId() != B.getId()
    assert A.getId() == A.getId()
    assert B.getId() == B.getId()
    assert C.getId() == C.getId()
