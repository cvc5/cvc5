#!/usr/bin/env python3
###############################################################################
# Top contributors (to current version):
#   Andrew Reynolds
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple test file to interact with cvc5 via the interactive shell with
# define-fun-rec.
##

import sys
import pexpect

def error_message(s):
    return "Unexpected output '" + s + "'"

def expect_exact(child, s):
    child.expect_exact(s)
    assert child.before == b"", error_message(child.before.decode('UTF-8'))
    assert child.after == s.encode('UTF-8'), error_message(child.after)

def sendline(child, s):
    child.sendline(s)
    expect_exact(child, s+'\r\n')

def check_iteractive_shell_define_fun_rec_multiline():
    """
    Interacts with cvc5's interactive shell and checks that define-fun-rec
    commands that span multiple lines are properly handled.
    """

    # Open cvc5
    child = pexpect.spawn("bin/cvc5", timeout=1)
    # We expect to see the cvc5 prompt
    child.expect("cvc5> ")
    sendline(child, "(set-logic ALL)")
    expect_exact(child, "cvc5> ")
    sendline(child, "(define-fun-rec")
    expect_exact(child, "... > ")
    sendline(child, "p () Bool")
    expect_exact(child, "... > ")
    sendline(child, "false)")
    expect_exact(child, "cvc5> ")
    sendline(child, "(define-funs-rec")
    expect_exact(child, "... > ")
    sendline(child, "((q () Bool))")
    expect_exact(child, "... > ")
    sendline(child, "(false))")
    expect_exact(child, "cvc5> ")
    sendline(child,"(assert (or p q))")
    expect_exact(child, "cvc5> ")
    sendline(child,"(check-sat)")
    expect_exact(child,"unsat\r\ncvc5> ")

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
    sys.exit(check_iteractive_shell_define_fun_rec_multiline())

if __name__ == "__main__":
    main()

# EOF
