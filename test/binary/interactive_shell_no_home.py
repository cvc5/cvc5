#!/usr/bin/env python3
###############################################################################
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Interactive shell must start when HOME is unset.
##

import os
import sys
import pexpect

def check_interactive_shell_no_home():
    """
    Start the interactive shell without HOME. The editline history path is
    built from getenv("HOME"); an unset HOME must not crash.
    """

    env = os.environ.copy()
    env.pop("HOME", None)

    child = pexpect.spawnu("bin/cvc5", timeout=2, env=env)
    child.expect("cvc5>")
    child.sendline("(exit)")
    child.expect(pexpect.EOF)

    # Reap the child so that we can inspect how it terminated. Without HOME the
    # destructor must skip write_history() rather than crash on shutdown, so a
    # clean EOF alone is not enough to consider this a pass.
    child.close()

    if child.signalstatus is not None:
        print(
            "cvc5 was killed by signal {} with HOME unset".format(
                child.signalstatus
            ),
            file=sys.stderr,
        )
        return 1

    if child.exitstatus != 0:
        print(
            "cvc5 exited with status {} with HOME unset".format(
                child.exitstatus
            ),
            file=sys.stderr,
        )
        return 1

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
    sys.exit(check_interactive_shell_no_home())

if __name__ == "__main__":
    main()

# EOF
