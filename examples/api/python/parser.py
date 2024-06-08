#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Daniel Larraz, Andrew Reynolds
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple demonstration of using the parser via Python API
##

import cvc5

if __name__ == "__main__":
    tm = cvc5.TermManager()
    slv = cvc5.Solver()

    # set that we should print success after each successful command
    slv.setOption("print-success", "true")

    # construct an input parser associated the solver above
    parser = cvc5.InputParser(slv)

    input = """
        (set-logic QF_LIA)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (declare-fun c () Int)
        (assert (> a (+ b c)))
        (assert (< a b))
        (assert (> c 0))
    """

    parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, input, "MyInput")

    # get the symbol manager of the parser, used when invoking commands below
    sm = parser.getSymbolManager()

    # parse commands until finished
    while True:
        cmd = parser.nextCommand()
        if cmd.isNull():
            break
        print(f"Executing command {cmd}:")
        # invoke the command on the solver and the symbol manager, print the result
        print(cmd.invoke(slv, sm), end="")

    print("Finished parsing commands")

    # now, check sat with the solver
    r = slv.checkSat()
    print("expected: unsat")
    print(f"result: {r}")
