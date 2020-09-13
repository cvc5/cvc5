#!/usr/bin/env python
#####################
#! \file sygus-fun.py
## \verbatim
## Top contributors (to current version):
##   Yoni Zohar
## This file is part of the CVC4 project.
## Copyright (c) 2009-2018 by the authors listed in the file AUTHkinds.OrS
## in the top-level source directory) and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.\endverbatim
##
## \brief A simple demonstration of the solving capabilities of the CVC4
## sygus solver through the Python API. This is a direct
## translation of sygus-fun.cpp.
#####################

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

  # declare input variables for the functions-to-synthesize
  x = slv.mkVar(integer, "x")
  y = slv.mkVar(integer, "y")

  # declare the grammar non-terminals
  start = slv.mkVar(integer, "Start")
  start_bool = slv.mkVar(boolean, "StartBool")

  # define the rules
  zero = slv.mkReal(0)
  one = slv.mkReal(1)

  plus = slv.mkTerm(kinds.Plus, start, start)
  minus = slv.mkTerm(kinds.Minus, start, start)
  ite = slv.mkTerm(kinds.Ite, start_bool, start, start)

  And = slv.mkTerm(kinds.And, start_bool, start_bool)
  Not = slv.mkTerm(kinds.Not, start_bool)
  leq = slv.mkTerm(kinds.Leq, start, start)

  # create the grammar object
  g = slv.mkSygusGrammar([x, y], [start, start_bool])

  # bind each non-terminal to its rules
  g.addRules(start, {zero, one, x, y, plus, minus, ite})
  g.addRules(start_bool, {And, Not, leq})

  # declare the functions-to-synthesize. Optionally, provide the grammar
  # constraints
  max = slv.synthFun("max", [x, y], integer, g)
  min = slv.synthFun("min", [x, y], integer)

  # declare universal variables.
  varX = slv.mkSygusVar(integer, "x")
  varY = slv.mkSygusVar(integer, "y")

  max_x_y = slv.mkTerm(kinds.ApplyUf, max, varX, varY)
  min_x_y = slv.mkTerm(kinds.ApplyUf, min, varX, varY)

  # add semantic constraints
  # (constraint (>= (max x y) x))
  slv.addSygusConstraint(slv.mkTerm(kinds.Geq, max_x_y, varX))

  # (constraint (>= (max x y) y))
  slv.addSygusConstraint(slv.mkTerm(kinds.Geq, max_x_y, varY))

  # (constraint (or (= x (max x y))
  #                 (= y (max x y))))
  slv.addSygusConstraint(slv.mkTerm(
      kinds.Or, slv.mkTerm(kinds.Equal, max_x_y, varX), slv.mkTerm(kinds.Equal, max_x_y, varY)))

  # (constraint (= (+ (max x y) (min x y))
  #                (+ x y)))
  slv.addSygusConstraint(slv.mkTerm(
      kinds.Equal, slv.mkTerm(kinds.Plus, max_x_y, min_x_y), slv.mkTerm(kinds.Plus, varX, varY)))

  # print solutions if available
  if (slv.checkSynth().isUnsat()):
    # Output should be equivalent to:
    # (define-fun max ((x Int) (y Int)) Int (ite (<= x y) y x))
    # (define-fun min ((x Int) (y Int)) Int (ite (<= x y) x y))
    slv.printSynthSolution()

