#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Aina Niemetz, Andrew Reynolds
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple demonstration of the solving capabilities of the cvc5
# sygus solver through the Python API. This is a direct
# translation of sygus-inv.cpp .
##

import utils
import cvc5
from cvc5 import Kind

if __name__ == "__main__":
  tm = cvc5.TermManager()
  slv = cvc5.Solver(tm)

  # required options
  slv.setOption("sygus", "true")
  slv.setOption("incremental", "false")

  # set the logic
  slv.setLogic("LIA")

  integer = tm.getIntegerSort()
  boolean = tm.getBooleanSort()

  zero = tm.mkInteger(0)
  one = tm.mkInteger(1)
  ten = tm.mkInteger(10)

  # declare input variables for functions
  x = tm.mkVar(integer, "x")
  xp = tm.mkVar(integer, "xp")

  # (ite (< x 10) (= xp (+ x 1)) (= xp x))
  ite = tm.mkTerm(Kind.ITE,
                   tm.mkTerm(Kind.LT, x, ten),
                   tm.mkTerm(Kind.EQUAL, xp, tm.mkTerm(Kind.ADD, x, one)),
                   tm.mkTerm(Kind.EQUAL, xp, x))

  # define the pre-conditions, transition relations, and post-conditions
  pre_f = slv.defineFun("pre-f", [x], boolean, tm.mkTerm(Kind.EQUAL, x, zero))
  trans_f = slv.defineFun("trans-f", [x, xp], boolean, ite)
  post_f = slv.defineFun("post-f", [x], boolean, tm.mkTerm(Kind.LEQ, x, ten))

  # declare the invariant-to-synthesize
  inv_f = slv.synthFun("inv-f", [x], boolean)

  slv.addSygusInvConstraint(inv_f, pre_f, trans_f, post_f)

  # print solutions if available
  if slv.checkSynth().hasSolution():
    # Output should be equivalent to:
    # (define-fun inv-f ((x Int)) Bool (not (>= x 11)))
    terms = [inv_f]
    utils.print_synth_solutions(terms, slv.getSynthSolutions(terms))


