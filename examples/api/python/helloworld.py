#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Makai Mann, Aina Niemetz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A very simple example, adapted from helloworld-new.cpp
##

import pycvc5
from pycvc5 import kinds

if __name__ == "__main__":
    slv = pycvc5.Solver()
    helloworld = slv.mkConst(slv.getBooleanSort(), "Hello World!")
    print(helloworld, "is", slv.checkEntailed(helloworld))
