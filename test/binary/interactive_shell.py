#!/usr/bin/env python3
###############################################################################
# Top contributors (to current version):
#   Andrew V. Jones, Mathias Preiner, Aina Niemetz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple test file to interact with cvc5 with line editing
##

import sys
import pexpect

def check_iteractive_shell():
    """
    Interacts with cvc5's interactive shell and checks that things such a tab
    completion and "pressing up" works.
    """

    # Open cvc5
    child = pexpect.spawnu("bin/cvc5", timeout=1)

    # We expect to see the cvc5 prompt
    child.expect("cvc5>")

    # If we send a line with just 'BOOLE' ...
    child.sendline("(set-log")

    # ... then we get an error
    child.expect("Expected SMT-LIBv2 command.")

    # Start sending 'BOOL' (without an E)
    child.send("(declare-data")

    # Send tab twice
    child.sendcontrol("i")
    child.sendcontrol("i")

    # We expect to see the completion
    child.expect("declare-datatype.*declare-datatypes")

    # NOTE: the double tab has completed our '(declare-data' to '(declare-datatype'!

    # Now send enter (which submits '(declare-datatype')
    child.send(")")
    child.sendcontrol("m")

    # So we expect to see an error for 'BOOLE'
    child.expect("Expected SMT-LIBv2 symbol")

    # Send enter
    child.sendcontrol("m")

    # We expect to see the cvc5 prompt
    child.expect("cvc5>")

    # Now send an up key
    child.send("\033[A")

    # Send enter
    child.sendcontrol("m")

    # We expect to see the previous error again
    child.expect("Expected SMT-LIBv2 symbol")

    return 0


def main():
    """
    Runs our interactive shell test

    Caveats:

        * If we don't have the "pexpect" model, the test doesn't get run, but
          passes

        * We expect pexpect to raise and exit with a non-zero exit code if any
          of the steps fail
    """

    # If any of the "steps" fail, the pexpect will raise a Python will exit
    # with a non-zero error code
    sys.exit(check_iteractive_shell())

if __name__ == "__main__":
    main()

# EOF
