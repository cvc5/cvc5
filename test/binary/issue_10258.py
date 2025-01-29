#!/usr/bin/env python3
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
# Regression test for issue #10258
##
import subprocess

class NonEmptyOutput(Exception):
    def __init__(self, output):
        super().__init__(output)

def main():
    echo_cmd = """echo '
        (set-logic ALL)
        (push 1)
        (declare-const z Int)
        (pop 1)
        (push 1)
        (declare-const z Int)
        (pop 1)'"""
    
    out = subprocess.check_output(echo_cmd + " | bin/cvc5 --lang smt2 --incremental", shell=True)
    if out != b'':
        raise NonEmptyOutput(out)

if __name__ == "__main__":
    main()
