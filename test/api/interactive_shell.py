#!/usr/bin/env python3
#####################
## interactive_shell.py
## Top contributors (to current version):
##   Andrew V. Jones
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##

#####################
#! \file interactive_shell.py
## \verbatim
## Top contributors (to current version):
##   Andrew V. Jones
## This file is part of the CVC4 project.
## Copyright (c) 2020 by the authors listed in the file AUTHORS
## in the top-level source directory) and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.\endverbatim
##
## \brief A simple test file to interact with CVC4 with line editing
#####################

import sys
import pexpect

def check_iteractive_shell():
    """
    Interacts with CVC4's interactive shell and checks that things such a tab
    completion and "pressing up" works.
    """

    # Open CVC4
    child = pexpect.spawnu("bin/cvc4", timeout=1)

    # We expect to see the CVC4 prompt
    child.expect("CVC4>")

    # If we send a line with just 'BOOLE' ...
    child.sendline("BOOLE")

    # ... then we get an error
    child.expect("Parse Error: <shell>:...: Unexpected token: 'BOOLE'")

    # Start sending 'BOOL' (without an E)
    child.send("BOOL")

    # Send tab twice
    child.sendcontrol("i")
    child.sendcontrol("i")

    # We expect to see the completion
    child.expect("BOOL.*BOOLEAN.*BOOLEXTRACT")

    # NOTE: the double tab has completed our 'BOOL' to 'BOOLE'!

    # Now send enter (which submits 'BOOLE')
    child.sendcontrol("m")

    # So we expect to see an error for 'BOOLE'
    child.expect("Parse Error: <shell>:...: Unexpected token: 'BOOLE'")

    # Send enter
    child.sendcontrol("m")

    # We expect to see the CVC4 prompt
    child.expect("CVC4>")

    # Now send an up key
    child.send("\033[A")

    # Send enter
    child.sendcontrol("m")

    # We expect to see an error on 'BOOLE' again
    child.expect("Parse Error: <shell>:...: Unexpected token: 'BOOLE'")

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
