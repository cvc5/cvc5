#! /usr/bin/python
##! \file SimpleVC.py
### \verbatim
### Original author: mdeters
### Major contributors: none
### Minor contributors (to current version): none
### This file is part of the CVC4 prototype.
### Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
### Courant Institute of Mathematical Sciences
### New York University
### See the file COPYING in the top-level source directory for licensing
### information.\endverbatim
###
### \brief A simple demonstration of the Python interface
###
### A simple demonstration of the Python interface.  Compare to the
### C++ interface in simple_vc_cxx.cpp; they are quite similar.
###
### To run from a build directory, use something like:
###
###   PYTHONPATH=src/bindings/python python ../examples/SimpleVC.py
####

import CVC4
from CVC4 import ExprManager, SmtEngine, Rational, Expr

import sys

def main():
  em = ExprManager()
  smt = SmtEngine(em)

  # Prove that for integers x and y:
  #   x > 0 AND y > 0  =>  2x + y >= 3

  integer = em.integerType()

  x = em.mkVar("x", integer)
  y = em.mkVar("y", integer)
  zero = em.mkConst(Rational(0))

  x_positive = em.mkExpr(CVC4.GT, x, zero)
  y_positive = em.mkExpr(CVC4.GT, y, zero)

  two = em.mkConst(Rational(2))
  twox = em.mkExpr(CVC4.MULT, two, x)
  twox_plus_y = em.mkExpr(CVC4.PLUS, twox, y)

  three = em.mkConst(Rational(3))
  twox_plus_y_geq_3 = em.mkExpr(CVC4.GEQ, twox_plus_y, three)

  formula = Expr(em.mkExpr(CVC4.AND, x_positive, y_positive)).impExpr(Expr(twox_plus_y_geq_3))

  print("Checking entailment of formula " + formula.toString() + " with CVC4.")
  print("CVC4 should report ENTAILED .")
  print("Result from CVC4 is: " + smt.checkEntailed(formula).toString())

  return 0

if __name__ == '__main__':
  sys.exit(main())
