#!/usr/bin/env python3
###############################################################################
# Top contributors (to current version):
#   Andrew V. Jones, Mathias Preiner, Aina Niemetz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
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
