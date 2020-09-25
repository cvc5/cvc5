#!/usr/bin/env python
#####################
## sygus-grammar.py
## Top contributors (to current version):
##   Yoni Zohar
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
## A simple demonstration of the solving capabilities of the CVC4
## sygus solver through the Python API. This is a direct
## translation of sygus-grammar.cpp.
##

import copy
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

  # declare input variable for the function-to-synthesize
  x = slv.mkVar(integer, "x")

  # declare the grammar non-terminal
  start = slv.mkVar(integer, "Start")

  # define the rules
  zero = slv.mkReal(0)
  neg_x = slv.mkTerm(kinds.Uminus, x)
  plus = slv.mkTerm(kinds.Plus, x, start)

  # create the grammar object
  g1 = slv.mkSygusGrammar({x}, {start})
  g2 = slv.mkSygusGrammar({x}, {start})
  g3 = slv.mkSygusGrammar({x}, {start})

  # bind each non-terminal to its rules
  g1.addRules(start, {neg_x, plus})
  g2.addRules(start, {neg_x, plus})
  g3.addRules(start, {neg_x, plus})

  # add parameters as rules for the start symbol. Similar to "(Variable Int)"
  g2.addAnyVariable(start)

  # declare the functions-to-synthesize
  id1 = slv.synthFun("id1", {x}, integer, g1)
  id2 = slv.synthFun("id2", {x}, integer, g2)

  g3.addRule(start, zero)

  id3 = slv.synthFun("id3", {x}, integer, g3)

  # g1 is reusable as long as it remains unmodified after first use
  id4 = slv.synthFun("id4", {x}, integer, g1)

  # declare universal variables.
  varX = slv.mkSygusVar(integer, "x")

  id1_x = slv.mkTerm(kinds.ApplyUf, id1, varX)
  id2_x = slv.mkTerm(kinds.ApplyUf, id2, varX)
  id3_x = slv.mkTerm(kinds.ApplyUf, id3, varX)
  id4_x = slv.mkTerm(kinds.ApplyUf, id4, varX)

  # add semantic constraints
  # (constraint (= (id1 x) (id2 x) (id3 x) (id4 x) x))
  slv.addSygusConstraint(slv.mkTerm(kinds.And, [slv.mkTerm(kinds.Equal, id1_x, id2_x), slv.mkTerm(kinds.Equal, id1_x, id3_x), slv.mkTerm(kinds.Equal, id1_x, id4_x), slv.mkTerm(kinds.Equal, id1_x, varX)]))

  # print solutions if available
  if (slv.checkSynth().isUnsat()):
    # Output should be equivalent to:
    # (define-fun id1 ((x Int)) Int (+ x (+ x (- x))))
    # (define-fun id2 ((x Int)) Int x)
    # (define-fun id3 ((x Int)) Int (+ x 0))
    # (define-fun id4 ((x Int)) Int (+ x (+ x (- x))))
    slv.printSynthSolution()
