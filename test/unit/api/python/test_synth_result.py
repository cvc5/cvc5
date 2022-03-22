###############################################################################
# Top contributors (to current version):
#   Andrew Reynolds
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Unit tests for synth result API.
#
# Obtained by translating test/unit/api/synth_result_black.cpp
##

import pytest
import cvc5
from cvc5 import SynthResult


@pytest.fixture
def solver():
    return cvc5.Solver()


def test_is_null(solver):
    res_null = SynthResult(solver)
    assert res_null.isNull()
    assert not res_null.hasSolution()
    assert not res_null.hasNoSolution()
    assert not res_null.isUnknown()
