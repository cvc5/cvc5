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
# A simple demonstration of using multiple parsers with the same symbol manager
# via Python API
##

import cvc5

if __name__ == "__main__":
    tm = cvc5.TermManager()
    slv = cvc5.Solver(tm)

    sm = cvc5.SymbolManager(slv)

    # construct an input parser associated the solver above
    parser = cvc5.InputParser(slv, sm)

    input = """
        (set-logic QF_LIA)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (declare-fun c () Bool)
    """

    parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, input, "MyInput")

    # parse commands until finished
    while True:
        cmd = parser.nextCommand()
        if cmd.isNull():
            break
        print(f"Executing command {cmd}")
        # invoke the command on the solver and the symbol manager, print the result
        print(cmd.invoke(slv, sm), end="")

    print("Finished parsing commands")

    # Note that sm now has a,b,c in its symbol table.

    # Now, construct a new parser with the same symbol manager. We will parse
    #terms with it.
    parser2 = cvc5.InputParser(slv, sm)

    parser2.setIncrementalStringInput(cvc5.InputLanguage.SMT_LIB_2_6, "MyInput2")

    input2 = """
        (+ a b)
        (- a 10)
        (>= 0 45)
        (and c c)
        true
    """
    parser2.appendIncrementalStringInput(input2)

    t = parser2.nextTerm()
    while not t.isNull():
        print(f"Parsed term: {t}")
        t = parser2.nextTerm()

    print("Finished parsing terms")
