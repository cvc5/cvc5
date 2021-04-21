###############################################################################
# Top contributors (to current version):
#   Yoni Zohar
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
##

import pytest
import pycvc5
import sys

from pycvc5 import kinds

@pytest.fixture
def solver():
    return pycvc5.Solver()

def test_recoverable_exception(solver):
    solver.setOption("produce-models", "true")
    x = solver.mkConst(solver.getBooleanSort(), "x")
    solver.assertFormula(x.eqTerm(x).notTerm())
    with pytest.raises(RuntimeError):
        c = solver.getValue(x)

def test_supports_floating_point(solver):
    if solver.supportsFloatingPoint():
      try:
          solver.mkRoundingMode(pycvc5.RoundNearestTiesToEven)
      except RuntimeError:
          pytest.fail()
    else:
        with pytest.raises(RuntimeError):
          solver.mkRoundingMode(pycvc5.RoundNearestTiesToEven)
