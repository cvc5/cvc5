#!/usr/bin/env python3
###############################################################################
# Top contributors (to current version):
#   Andrew Reynolds
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple test file to interact with cvc5 via the interactive shell in
# incremental mode.
##

import sys
import pexpect

def check_iteractive_shell_parser_inc():
    """
    Interacts with cvc5's interactive shell and checks that parser declarations are
    managed properly in incremental mode.
    """

    # Open cvc5
    child = pexpect.spawnu("bin/cvc5", timeout=1)

    # We expect to see the cvc5 prompt
    child.expect("cvc5>")

    child.sendline("(set-option :incremental true)")
    child.sendline("(push)")
    child.sendline("(declare-fun x () Int)")
    child.sendline("(check-sat)")
    child.expect("sat")
    child.sendline("(pop)")
    child.sendline("(declare-fun x () Int)")
    child.expect("")
    child.sendline("(check-sat)")
    child.expect("sat")

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
    sys.exit(check_iteractive_shell_parser_inc())

if __name__ == "__main__":
    main()

# EOF
