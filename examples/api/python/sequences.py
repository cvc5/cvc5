#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Andres Noetzli, Makai Mann, Aina Niemetz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple demonstration of the solving capabilities of the cvc5 strings solver
# through the Python API. This is a direct translation of sequences.cpp.
##

import cvc5
from cvc5 import Kind

if __name__ == "__main__":
    slv = cvc5.Solver()
    # Set the logic
    slv.setLogic("QF_SLIA")
    # Produce models
    slv.setOption("produce-models", "true")
    # The option strings-exp is needed
    slv.setOption("strings-exp", "true")
    # Set output language to SMTLIB2
    slv.setOption("output-language", "smt2")

    # Sequence sort
    int_seq = slv.mkSequenceSort(slv.getIntegerSort())

    # Sequence variables
    x = slv.mkConst(int_seq, "x")
    y = slv.mkConst(int_seq, "y")

    # Empty sequence
    empty = slv.mkEmptySequence(slv.getIntegerSort())
    # Sequence concatenation: x.y.empty
    concat = slv.mkTerm(Kind.SEQ_CONCAT, x, y, empty)
    # Sequence length: |x.y.empty|
    concat_len = slv.mkTerm(Kind.SEQ_LENGTH, concat)
    # |x.y.empty| > 1
    formula1 = slv.mkTerm(Kind.GT, concat_len, slv.mkInteger(1))
    # Sequence unit: seq(1)
    unit = slv.mkTerm(Kind.SEQ_UNIT, slv.mkInteger(1))
    # x = seq(1)
    formula2 = slv.mkTerm(Kind.EQUAL, x, unit)

    # Make a query
    q = slv.mkTerm(Kind.AND, formula1, formula2)

    # Check satisfiability
    result = slv.checkSatAssuming(q)
    print("cvc5 reports:", q, "is", result)

    if result:
        print("x = {}".format(slv.getValue(x)))
        print("y = {}".format(slv.getValue(y)))
