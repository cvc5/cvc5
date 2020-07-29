#!/usr/bin/env python

#####################
#! \file sygus-inv.py
## \verbatim
## Top contributors (to current version):
##   Yoni Zohar
## This file is part of the CVC4 project.
## Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
## in the top-level source directory) and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.\endverbatim
##
## \brief A simple demonstration of the solving capabilities of the CVC4
## sygus solver through the Python API. This is a direct
## translation of sygus-inv.cpp .
#####################

import pycvc4
from pycvc4 import kinds

if __name__ == "__main__":
  slv = pycvc4.Solver()

  # required options
  slv.setOption("lang", "sygus2")
  slv.setOption("incremental", "false")

  # set the logic
  slv.setLogic("LIA")

  integer = slv.getIntegerSort()
  boolean = slv.getBooleanSort()

  zero = slv.mkReal(0)
  one = slv.mkReal(1)
  ten = slv.mkReal(10)

  # declare input variables for functions
  x = slv.mkVar(integer, "x")
  xp = slv.mkVar(integer, "xp")

  # (ite (< x 10) (= xp (+ x 1)) (= xp x))
  ite = slv.mkTerm(kinds.Ite,
                        slv.mkTerm(kinds.Lt, x, ten),
                        slv.mkTerm(kinds.Equal, xp, slv.mkTerm(kinds.Plus, x, one)),
                        slv.mkTerm(kinds.Equal, xp, x))

  # define the pre-conditions, transition relations, and post-conditions
  pre_f = slv.defineFun("pre-f", {x}, boolean, slv.mkTerm(kinds.Equal, x, zero))
  trans_f = slv.defineFun("trans-f", {x, xp}, boolean, ite)
  post_f = slv.defineFun("post-f", {x}, boolean, slv.mkTerm(kinds.Leq, x, ten))

  # declare the invariant-to-synthesize
  inv_f = slv.synthInv("inv-f", {x})

  slv.addSygusInvConstraint(inv_f, pre_f, trans_f, post_f)

  # print solutions if available
  if slv.checkSynth().isUnsat():
    # Output should be equivalent to:
    # (define-fun inv-f ((x Int)) Bool (not (>= x 11)))
    slv.printSynthSolution()



