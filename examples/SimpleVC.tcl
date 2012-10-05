#! /usr/bin/tclsh
##! \file SimpleVC.tcl
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
### \brief A simple demonstration of the Tcl interface
###
### A simple demonstration of the Tcl interface.  Compare to the
### C++ interface in simple_vc_cxx.cpp; they are quite similar.
###
### To run, use something like:
###
###   ln -s ../builds/src/bindings/tcl/.libs/CVC4.so CVC4.so
###   ./SimpleVC.tcl
####

load CVC4.so CVC4

ExprManager em
SmtEngine smt em

# Prove that for integers x and y:
#   x > 0 AND y > 0  =>  2x + y >= 3

set integer [ExprManager_integerType em]

set x [ExprManager_mkVar em "x" $integer]
set y [ExprManager_mkVar em "y" $integer]
set zero [ExprManager_mkConst em [Integer _ 0]]

set x_positive [ExprManager_mkExpr em $GT $x $zero]
set y_positive [ExprManager_mkExpr em $GT $y $zero]

set two [ExprManager_mkConst em [Integer _ 2]]
set twox [ExprManager_mkExpr em $MULT $two $x]
set twox_plus_y [ExprManager_mkExpr em $PLUS $twox $y]

set three [ExprManager_mkConst em [Integer _ 3]]
set twox_plus_y_geq_3 [ExprManager_mkExpr em $GEQ $twox_plus_y $three]

set formula [Expr_impExpr [Expr _1 [ExprManager_mkExpr em $AND $x_positive $y_positive]] [Expr _2 $twox_plus_y_geq_3]]

puts "Checking validity of formula [Expr_toString $formula] with CVC4."
puts "CVC4 should report VALID."
puts "Result from CVC4 is: [Result_toString [SmtEngine_query smt $formula]]"

