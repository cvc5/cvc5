#! /usr/bin/ruby
##! \file SimpleVC.rb
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
### \brief A simple demonstration of the Ruby interface
###
### A simple demonstration of the Ruby interface.  Compare to the
### C++ interface in simple_vc_cxx.cpp; they are quite similar.
###
### To run, use something like:
###
###   ln -s ../builds/src/bindings/ruby/.libs/CVC4.so CVC4.so
###   ./SimpleVC.rb
####

require 'CVC4'
include CVC4 # CVC4::Integer still has to be qualified

em = ExprManager.new
smt = SmtEngine.new(em)

# Prove that for integers x and y:
#   x > 0 AND y > 0  =>  2x + y >= 3

integer = em.integerType

x = em.mkVar("x", integer)
y = em.mkVar("y", integer)
zero = em.mkConst(CVC4::Integer.new(0))

x_positive = em.mkExpr(GT, x, zero)
y_positive = em.mkExpr(GT, y, zero)

two = em.mkConst(CVC4::Integer.new(2))
twox = em.mkExpr(MULT, two, x)
twox_plus_y = em.mkExpr(PLUS, twox, y)

three = em.mkConst(CVC4::Integer.new(3))
twox_plus_y_geq_3 = em.mkExpr(GEQ, twox_plus_y, three)

formula = Expr.new(em.mkExpr(AND, x_positive, y_positive)).impExpr(Expr.new(twox_plus_y_geq_3))

puts "Checking validity of formula " + formula.toString + " with CVC4."
puts "CVC4 should report VALID."
puts "Result from CVC4 is: " + smt.query(formula).toString

exit

