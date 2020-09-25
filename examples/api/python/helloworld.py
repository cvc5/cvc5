#!/usr/bin/env python
#####################
## helloworld.py
## Top contributors (to current version):
##   Makai Mann, Aina Niemetz
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##
## A very simple CVC4 tutorial example, adapted from helloworld-new.cpp
##

import pycvc4
from pycvc4 import kinds

if __name__ == "__main__":
    slv = pycvc4.Solver()
    helloworld = slv.mkConst(slv.getBooleanSort(), "Hello World!")
    print(helloworld, "is", slv.checkEntailed(helloworld))
