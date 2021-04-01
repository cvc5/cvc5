#####################
## test_term.py
## Top contributors (to current version):
##   Yoni Zohar
## This file is part of the CVC4 project.
## Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
import pytest
import pycvc4
import sys

from pycvc4 import kinds

class TestSolver:
    def setup_class(self):
        self.solver = pycvc4.Solver()

    def test_recoverableException(self):
        self.solver.setOption("produce-models", "true")
        x = self.solver.mkConst(self.solver.getBooleanSort(), "x")
        self.solver.assertFormula(x.eqTerm(x).notTerm())
        with pytest.raises(Exception):
            c = self.solver.get_value(x)

    def test_supportsFloatingPoint(self):
        if self.solver.supportsFloatingPoint():
          try:
              self.solver.mkRoundingMode(ROUND_NEAREST_TIES_TO_EVEN)
          except Exception:
              pytest.fail()
        else:
            with pytest.raises(Exception):
                self.solver.mkRoundingMode(ROUND_NEAREST_TIES_TO_EVEN)
