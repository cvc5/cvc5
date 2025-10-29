###############################################################################
# Top contributors (to current version):
#   Daniel Larraz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A test of SMT-LIBv2 commands, checks for compliant output.
##

import cvc5

def test_get_info(solver, key):
    sm = cvc5.SymbolManager(solver.getTermManager())
    parser = cvc5.InputParser(solver, sm)

    input_str = f"(get-info {key})"
    parser.setStringInput(cvc5.InputLanguage.SMT_LIB_2_6, input_str, "<internal>")

    cmd = parser.nextCommand()
    assert (not cmd.isNull())
    print(f"{cmd}")

    output_str = cmd.invoke(solver, sm)

    cmd = parser.nextCommand()
    assert cmd.isNull()
    print(output_str)
 

tm = cvc5.TermManager()
solver = cvc5.Solver(tm)
solver.setOption("input-language", "smtlib2")
solver.setOption("output-language", "smtlib2")

test_get_info(solver, ":error-behavior")
test_get_info(solver, ":name")
test_get_info(solver, ":authors")
test_get_info(solver, ":version")
test_get_info(solver, ":status")
test_get_info(solver, ":reason-unknown")
test_get_info(solver, ":arbitrary-undefined-keyword")
test_get_info(solver, ":<=")   # legal
test_get_info(solver, ":->")   # legal
test_get_info(solver, ":all-statistics")
