/*********************                                                        */
/*! \file simple_vc_cxx.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Dejan Jovanovic, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A simple demonstration of the C++ interface
 **
 ** A simple demonstration of the C++ interface.  Compare to the Java
 ** interface in SimpleVC.java; they are virtually line-by-line
 ** identical.
 **/

#include <cvc4/api/cvc4cpp.h>

#include <iostream>

using namespace CVC4::api;

int main() {
  Solver slv;

  // Prove that for integers x and y:
  //   x > 0 AND y > 0  =>  2x + y >= 3

  Sort integer = slv.getIntegerSort();

  Term x = slv.mkConst(integer, "x");
  Term y = slv.mkConst(integer, "y");
  Term zero = slv.mkReal(0);

  Term x_positive = slv.mkTerm(Kind::GT, x, zero);
  Term y_positive = slv.mkTerm(Kind::GT, y, zero);

  Term two = slv.mkReal(2);
  Term twox = slv.mkTerm(Kind::MULT, two, x);
  Term twox_plus_y = slv.mkTerm(Kind::PLUS, twox, y);

  Term three = slv.mkReal(3);
  Term twox_plus_y_geq_3 = slv.mkTerm(Kind::GEQ, twox_plus_y, three);

  Term formula =
      slv.mkTerm(Kind::AND, x_positive, y_positive).impTerm(twox_plus_y_geq_3);

  std::cout << "Checking entailment of formula " << formula << " with CVC4."
            << std::endl;
  std::cout << "CVC4 should report ENTAILED." << std::endl;
  std::cout << "Result from CVC4 is: " << slv.checkEntailed(formula)
            << std::endl;

  return 0;
}
