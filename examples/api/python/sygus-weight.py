#!/usr/bin/env python
###############################################################################
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A demonstration of the SyGuS 2.1 weight API.
#
# Synthesize 3*x using only `+` (weight 1) and `*` (weight 31), constrained
# to have a total `w` weight of 2. The expected solution is (+ x (+ x x)).
##

import cvc5
import utils
from cvc5 import Kind

if __name__ == "__main__":
    tm = cvc5.TermManager()
    slv = cvc5.Solver(tm)

    # required options
    slv.setOption("sygus", "true")
    slv.setOption("incremental", "false")

    # set the logic
    slv.setLogic("NIA")

    integer = tm.getIntegerSort()

    # declare input variables for the functions-to-synthesize
    x = tm.mkVar(integer, "x")

    # declare the grammar non-terminals
    start = tm.mkVar(integer, "Start")

    # define the rules
    zero = tm.mkInteger(0)
    one = tm.mkInteger(1)
    two = tm.mkInteger(2)
    three = tm.mkInteger(3)
    thirty_one = tm.mkInteger(31)

    add = tm.mkTerm(Kind.ADD, start, start)
    mult = tm.mkTerm(Kind.MULT, start, start)

    # declare a weight attribute with the default value of 0
    w = slv.declareWeight("w")

    # create the grammar object
    g = slv.mkGrammar([x], [start])

    # bind each non-terminal to its rules
    g.addRules(start, [zero, one, three, x])
    g.addRule(start, add, {w: one})
    g.addRule(start, mult, {w: thirty_one})

    # declare the function-to-synthesize
    f = slv.synthFun("f", [x], integer, g)

    # declare universal variables
    var_x = slv.declareSygusVar("x", integer)

    f_of_x = tm.mkTerm(Kind.APPLY_UF, f, var_x)
    three_x = tm.mkTerm(Kind.MULT, three, var_x)

    # add the semantic constraint: (= (f x) (* 3 x))
    slv.addSygusConstraint(tm.mkTerm(Kind.EQUAL, f_of_x, three_x))

    # declare the weight symbol (_ w f)
    w_f = slv.mkWeightSymbol(w, f)

    # add the weight constraint: (= (_ w f) 2)
    slv.addSygusConstraint(tm.mkTerm(Kind.EQUAL, w_f, two))

    # print the solution if available
    if slv.checkSynth().hasSolution():
        # Output should be equivalent to:
        # (define-fun f ((x Int)) Int (+ x (+ x x)))
        utils.print_synth_solutions([f], slv.getSynthSolutions([f]))
