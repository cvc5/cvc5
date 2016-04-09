/*********************                                                        */
/*! \file simple_vc_compat_cxx.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A simple demonstration of the C++ compatibility interface
 ** (quite similar to the old CVC3 C++ interface)
 **
 ** A simple demonstration of the C++ compatibility interface (quite
 ** similar to the old CVC3 C++ interface).  Note that the library is
 ** named "libcvc4compat," to mark it as being part of CVC4, but the
 ** header file is "cvc3_compat.h" to indicate the similarity to the
 ** CVC3 interface, and the namespace is "CVC3".  CVC3::Expr and
 ** CVC4::Expr are incompatible; to avoid confusion, it is best to not
 ** include both the CVC3 and CVC4 interface headers.
 **/

#include <iostream>

// #include <cvc4/compat/cvc3_compat.h> // use this after CVC4 is properly installed
#include "compat/cvc3_compat.h"

using namespace std;
using namespace CVC3;

int main() {
  ValidityChecker* vc = ValidityChecker::create();

  // Prove that for integers x and y:
  //   x > 0 AND y > 0  =>  2x + y >= 3

  Type integer = vc->intType();

  Expr x = vc->varExpr("x", integer);
  Expr y = vc->varExpr("y", integer);
  Expr zero = vc->ratExpr(0);

  Expr x_positive = vc->gtExpr(x, zero);
  Expr y_positive = vc->gtExpr(y, zero);

  Expr two = vc->ratExpr(2);
  Expr twox = vc->multExpr(two, x);
  Expr twox_plus_y = vc->plusExpr(twox, y);

  Expr three = vc->ratExpr(3);
  Expr twox_plus_y_geq_3 = vc->geExpr(twox_plus_y, three);

  Expr formula = vc->impliesExpr(vc->andExpr(x_positive, y_positive),
                                twox_plus_y_geq_3);

  cout << "Checking validity of formula " << formula << " with CVC4." << endl;
  cout << "CVC4 should report VALID." << endl;
  cout << "Result from CVC4 is: " << vc->query(formula) << endl;

  return 0;
}
