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
# An example demonstrating the ordering relation of set sorts.
##
from cvc5.pythonic import *

if __name__ == '__main__':
    A = Set("A", SetSort(IntSort()))
    B = Set("B", SetSort(IntSort()))
    C = Set("C", SetSort(IntSort()))

    assert A.get_id() != B.get_id()
    assert C.get_id() != B.get_id()
    assert A.get_id() == A.get_id()
    assert B.get_id() == B.get_id()
    assert C.get_id() == C.get_id()
