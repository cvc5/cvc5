#!/usr/bin/env python
#####################
## extract.py
## Top contributors (to current version):
##   Makai Mann, Aina Niemetz
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
## A simple demonstration of the solving capabilities of the CVC4
## bit-vector solver through the Python API. This is a direct translation
## of extract-new.cpp.
##

from pycvc4 import Solver
from pycvc4.kinds import BVExtract, Equal

if __name__ == "__main__":
    slv = Solver()
    slv.setLogic("QF_BV")

    bitvector32 = slv.mkBitVectorSort(32)

    x = slv.mkConst(bitvector32, "a")

    ext_31_1 = slv.mkOp(BVExtract, 31, 1)
    x_31_1 = slv.mkTerm(ext_31_1, x)

    ext_30_0 = slv.mkOp(BVExtract, 30, 0)
    x_30_0 = slv.mkTerm(ext_30_0, x)

    ext_31_31 = slv.mkOp(BVExtract, 31, 31)
    x_31_31 = slv.mkTerm(ext_31_31, x)

    ext_0_0 = slv.mkOp(BVExtract, 0, 0)
    x_0_0 = slv.mkTerm(ext_0_0, x)

    # test getting indices
    assert ext_30_0.getIndices() == (30, 0)

    eq = slv.mkTerm(Equal, x_31_1, x_30_0)
    print("Asserting:", eq)
    slv.assertFormula(eq)

    eq2 = slv.mkTerm(Equal, x_31_31, x_0_0)
    print("Check entailment assuming:", eq2)
    print("Expect ENTAILED")
    print("CVC4:", slv.checkEntailed(eq2))
