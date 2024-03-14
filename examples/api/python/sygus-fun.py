#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Aina Niemetz, Andrew Reynolds
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple demonstration of the solving capabilities of the cvc5 sygus solver
# through the Python API. This is a direct translation of sygus-fun.cpp.
##

import copy
import cvc5
import utils
from cvc5 import Kind

if __name__ == "__main__":
  tm = cvc5.TermManager()
  slv = cvc5.Solver()

  # required options
  slv.setOption("sygus", "true")
  slv.setOption("incremental", "false")

  # set the logic
  slv.setLogic("LIA")

  integer = tm.getIntegerSort()
  boolean = tm.getBooleanSort()

  # declare input variables for the functions-to-synthesize
  x = tm.mkVar(integer, "x")
  y = tm.mkVar(integer, "y")

  # declare the grammar non-terminals
  start = tm.mkVar(integer, "Start")
  start_bool = tm.mkVar(boolean, "StartBool")

  # define the rules
  zero = tm.mkInteger(0)
  one = tm.mkInteger(1)

  plus = tm.mkTerm(Kind.ADD, start, start)
  minus = tm.mkTerm(Kind.SUB, start, start)
  ite = tm.mkTerm(Kind.ITE, start_bool, start, start)

  And = tm.mkTerm(Kind.AND, start_bool, start_bool)
  Not = tm.mkTerm(Kind.NOT, start_bool)
  leq = tm.mkTerm(Kind.LEQ, start, start)

  # create the grammar object
  g = slv.mkGrammar([x, y], [start, start_bool])

  # bind each non-terminal to its rules
  g.addRules(start, [zero, one, x, y, plus, minus, ite])
  g.addRules(start_bool, [And, Not, leq])

  # declare the functions-to-synthesize. Optionally, provide the grammar
  # constraints
  max = slv.synthFun("max", [x, y], integer, g)
  min = slv.synthFun("min", [x, y], integer)

  # declare universal variables.
  varX = slv.declareSygusVar("x", integer)
  varY = slv.declareSygusVar("y", integer)

  max_x_y = tm.mkTerm(Kind.APPLY_UF, max, varX, varY)
  min_x_y = tm.mkTerm(Kind.APPLY_UF, min, varX, varY)

  # add semantic constraints
  # (constraint (>= (max x y) x))
  slv.addSygusConstraint(tm.mkTerm(Kind.GEQ, max_x_y, varX))

  # (constraint (>= (max x y) y))
  slv.addSygusConstraint(tm.mkTerm(Kind.GEQ, max_x_y, varY))

  # (constraint (or (= x (max x y))
  #                 (= y (max x y))))
  slv.addSygusConstraint(tm.mkTerm(
      Kind.OR,
      tm.mkTerm(Kind.EQUAL, max_x_y, varX),
      tm.mkTerm(Kind.EQUAL, max_x_y, varY)))

  # (constraint (= (+ (max x y) (min x y))
  #                (+ x y)))
  slv.addSygusConstraint(tm.mkTerm(
      Kind.EQUAL,
      tm.mkTerm(Kind.ADD, max_x_y, min_x_y),
      tm.mkTerm(Kind.ADD, varX, varY)))

  # print solutions if available
  if (slv.checkSynth().hasSolution()):
    # Output should be equivalent to:
    # (define-fun max ((x Int) (y Int)) Int (ite (<= x y) y x))
    # (define-fun min ((x Int) (y Int)) Int (ite (<= x y) x y))
    terms = [max, min]
    utils.print_synth_solutions(terms, slv.getSynthSolutions(terms))
