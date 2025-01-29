#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Aina Niemetz, Alex Ozdemir, Makai Mann
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A very simple example, adapted from helloworld-new.cpp
##

import cvc5
from cvc5 import Kind

if __name__ == "__main__":
    tm = cvc5.TermManager()
    slv = cvc5.Solver(tm)
    helloworld = tm.mkConst(tm.getBooleanSort(), "Hello World!")
    print(helloworld, "is", slv.checkSatAssuming(helloworld))
