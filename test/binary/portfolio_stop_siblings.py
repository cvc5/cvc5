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
# After a portfolio worker solves, remaining workers and timeout children
# must be reaped before the parent exits.
##

import os
import signal
import subprocess
import sys
import tempfile

SMT = """(set-logic QF_LRA)
(declare-fun x () Real)
(assert (> x 0.0))
(check-sat)
"""


def list_group(pgid):
    try:
        out = subprocess.check_output(["pgrep", "-g", str(pgid)], text=True)
    except (subprocess.CalledProcessError, OSError):
        return []
    pids = []
    for line in out.split():
        try:
            pids.append(int(line))
        except ValueError:
            pass
    return pids


def kill_group(pgid):
    try:
        os.killpg(pgid, signal.SIGKILL)
    except OSError:
        pass


def main():
    # Capture output in a file so leftover children that inherit stdout
    # cannot keep a pipe open and hide the parent's exit from communicate().
    with tempfile.NamedTemporaryFile(mode="w+", prefix="cvc5-portfolio-") as out:
        proc = subprocess.Popen(
            [
                "bin/cvc5",
                "--use-portfolio",
                "--portfolio-jobs=2",
                "--tlimit=60000",
                "-o",
                "portfolio",
            ],
            stdin=subprocess.PIPE,
            stdout=out,
            stderr=subprocess.STDOUT,
            text=True,
            start_new_session=True,
        )
        pgid = os.getpgid(proc.pid)
        leftover = []
        try:
            proc.stdin.write(SMT)
            proc.stdin.close()
            proc.wait(timeout=15)
            out.flush()
            out.seek(0)
            stdout = out.read()
            if "cannot be set in stable mode" in stdout or "cannot be set in safe mode" in stdout:
                print("skip: --use-portfolio is unavailable in this build")
                return 0
            if proc.returncode != 0:
                print(
                    "cvc5 exited {}\noutput:\n{}".format(proc.returncode, stdout),
                    file=sys.stderr,
                )
                return 1
            if "sat" not in stdout.split():
                print("expected sat, got:\n{}".format(stdout), file=sys.stderr)
                return 1
            leftover = [pid for pid in list_group(pgid) if pid != proc.pid]
            if leftover:
                print(
                    "leftover portfolio processes after parent exit: {}".format(
                        leftover
                    ),
                    file=sys.stderr,
                )
                return 1
            return 0
        except subprocess.TimeoutExpired:
            print("cvc5 timed out waiting for portfolio solve", file=sys.stderr)
            return 1
        finally:
            if proc.poll() is None:
                proc.kill()
                proc.wait()
            still = [pid for pid in list_group(pgid) if pid != proc.pid]
            if still:
                kill_group(pgid)


if __name__ == "__main__":
    sys.exit(main())
