######################                                                        ##
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
### To run, use something like:
###
###   PYTHONPATH=/dir/containing/CVC4.py:$PYTHONPATH \
###   python \
###     -Djava.library.path=/dir/containing/libcvc4bindings_python.so \
###     SimpleVC
####

from ctypes import cdll
cdll.LoadLibrary('libcvc4.so')
cdll.LoadLibrary('libcvc4parser.so')
cdll.LoadLibrary('libcvc4bindings_python.so')
import CVC4

def main():
  em = ExprManager()
  smt = SmtEngine(em)

  # Prove that for integers x and y:
  #   x > 0 AND y > 0  =>  2x + y >= 3

  integer = em.integerType()

  x = em.mkVar("x", integer)
  y = em.mkVar("y", integer)
  zero = em.mkConst(Integer(0))

  x_positive = em.mkExpr(kind.GT, x, zero)
  y_positive = em.mkExpr(kind.GT, y, zero)

  two = em.mkConst(Integer(2))
  twox = em.mkExpr(kind.MULT, two, x)
  twox_plus_y = em.mkExpr(kind.PLUS, twox, y)

  three = em.mkConst(Integer(3))
  twox_plus_y_geq_3 = em.mkExpr(kind.GEQ, twox_plus_y, three)

  formula = BoolExpr(em.mkExpr(kind.AND, x_positive, y_positive)).impExpr(BoolExpr(twox_plus_y_geq_3))

  print "Checking validity of formula " << formula << " with CVC4." << endl
  print "CVC4 should report VALID." << endl
  print "Result from CVC4 is: " << smt.query(formula) << endl

  return 0
