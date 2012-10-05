#! /usr/bin/php
##! \file SimpleVC.php
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
### \brief A simple demonstration of the PHP interface
###
### A simple demonstration of the PHP interface.  Compare to the
### C++ interface in simple_vc_cxx.cpp; they are quite similar.
###
### To run, use something like:
###
###   ln -s ../builds/src/bindings/php/.libs/CVC4.so CVC4.so
###   ln -s ../builds/src/bindings/php/CVC4.php CVC4.php
###   ./SimpleVC.php
####

use strict;
use CVC4;

my $em = new CVC4::ExprManager();
my $smt = new CVC4::SmtEngine($em);

# Prove that for integers x and y:
#   x > 0 AND y > 0  =>  2x + y >= 3

my $integer = $em->integerType();

my $x = $em->mkVar("x", $integer);
my $y = $em->mkVar("y", $integer);
my $zero = $em->mkConst(new CVC4::Integer(0));

my $x_positive = $em->mkExpr($CVC4::GT, $x, $zero);
my $y_positive = $em->mkExpr($CVC4::GT, $y, $zero);

my $two = $em->mkConst(new CVC4::Integer(2));
my $twox = $em->mkExpr($CVC4::MULT, $two, $x);
my $twox_plus_y = $em->mkExpr($CVC4::PLUS, $twox, $y);

my $three = $em->mkConst(new CVC4::Integer(3));
my $twox_plus_y_geq_3 = $em->mkExpr($CVC4::GEQ, $twox_plus_y, $three);

my $formula = new CVC4::Expr($em->mkExpr($CVC4::AND, $x_positive, $y_positive))->impExpr(new CVC4::Expr($twox_plus_y_geq_3));

print "Checking validity of formula " . $formula->toString() . " with CVC4.\n";
print "CVC4 should report VALID.\n";
print "Result from CVC4 is: " . $smt->query($formula)->toString() . "\n";

