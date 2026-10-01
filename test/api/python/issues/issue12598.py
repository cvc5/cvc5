###############################################################################
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Test for issue #12598
##

import cvc5

tm = cvc5.TermManager()
solver = cvc5.Solver(tm)
parser = cvc5.InputParser(solver)
parser.setStringInput(
    cvc5.InputLanguage.SMT_LIB_2_6,
    "(set-logic ALL)\n(declare-const p Bool)\n(assert p)\n(check-sat)\n",
    "repro",
)
cmd = parser.nextCommand()
try:
    cmd.invoke(solver, None)
    assert False, "Expected TypeError"
except TypeError as e:
    print(f"TypeError: {e}")