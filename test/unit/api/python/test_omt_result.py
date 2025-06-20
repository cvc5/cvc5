###############################################################################
# Top contributors (to current version):
#   Andrew Reynolds, Aina Niemetz, Gereon Kremer
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Unit tests for OMT result API.
#
# Obtained by translating test/unit/api/omt_result_black.cpp
##

import pytest
import cvc5
from cvc5 import OmtResult

def test_is_null_omtresult():
    res_null = OmtResult()
    assert res_null.isNull()
    assert not res_null.isOptimal()
    assert not res_null.isLimitOptimal()
    assert not res_null.isNonOptimal()
    assert not res_null.isUnbounded()
    assert not res_null.isUnsat()
    assert not res_null.isUnknown()
    assert str(res_null) == '(NONE)'

def test_equal():
    res1 = OmtResult()
    res2 = OmtResult()
    assert res1 == res1
    assert res1 == res2
    assert not res1 != res2
    assert res1 == OmtResult()