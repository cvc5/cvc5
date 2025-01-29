#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Yoni Zohar
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple demonstration of the solving capabilities of the cvc5 strings
# solver. A simple translation of the base python API example.
##

from cvc5.pythonic import *

if __name__ == "__main__":
    x = Const("x", SeqSort(IntSort()))
    y = Const("y", SeqSort(IntSort()))

    # Empty sequence
    empty = Empty(SeqSort(IntSort()))
    # Sequence concatenation: x.y.empty
    concat = Concat( x, y, empty)
    # Sequence length: |x.y.empty|
    concat_len = Length(concat)
    # |x.y.empty| > 1
    formula1 = (concat_len > 1)
    # Sequence unit: seq(1)
    unit = Unit(IntVal(1))
    # x = seq(1)
    formula2 = (x == unit)

    # Make a query
    q = And(formula1, formula2)

    # Check satisfiability
    s = Solver()
    result = s.check([q])
    assert result == sat
    m = s.model()
    print("x = {}".format(m[x]))
    print("y = {}".format(m[y]))
