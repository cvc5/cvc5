#!/usr/bin/env python

#####################
## \file exceptions.py
## \verbatim
## Top contributors (to current version):
##   Andres Noetzli
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory) and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.\endverbatim
##
## \brief Catching CVC4 exceptions with the legacy Python API.
##
## A simple demonstration of catching CVC4 execptions with the legacy Python
## API.

import CVC4
import sys


def main():
    em = CVC4.ExprManager()
    smt = CVC4.SmtEngine(em)

    smt.setOption("produce-models", CVC4.SExpr("true"))

    # Setting an invalid option
    try:
        smt.setOption("non-existing", CVC4.SExpr("true"))
        return 1
    except CVC4.Exception as e:
        print(e.toString())

    # Creating a term with an invalid type
    try:
        integer = em.integerType()
        x = em.mkVar("x", integer)
        invalidExpr = em.mkExpr(CVC4.AND, x, x)
        smt.checkSat(invalidExpr)
        return 1
    except CVC4.Exception as e:
        print(e.toString())

    # Asking for a model after unsat result
    try:
        smt.checkSat(em.mkBoolConst(False))
        smt.getModel()
        return 1
    except CVC4.Exception as e:
        print(e.toString())

    return 0


if __name__ == '__main__':
    sys.exit(main())
