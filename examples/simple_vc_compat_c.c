/*********************                                                        */
/*! \file simple_vc_compat_c.c
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A simple demonstration of the C compatibility interface
 ** (quite similar to the old CVC3 C interface)
 **
 ** A simple demonstration of the C compatibility interface
 ** (quite similar to the old CVC3 C interface).
 **/

#include <stdio.h>
#include <stdlib.h>

/* #include <cvc4/bindings/compat/c/c_interface.h> /* use this after CVC4 is properly installed */
#include "bindings/compat/c/c_interface.h"

int main() {
  VC vc = vc_createValidityChecker(NULL);

  /* Prove that for integers x and y:
   *   x > 0 AND y > 0  =>  2x + y >= 3 */

  Type integer = vc_intType(vc);

  Expr x = vc_varExpr(vc, "x", integer);
  Expr y = vc_varExpr(vc, "y", integer);
  Expr zero = vc_ratExpr(vc, 0, 1);

  Expr x_positive = vc_gtExpr(vc, x, zero);
  Expr y_positive = vc_gtExpr(vc, y, zero);

  Expr two = vc_ratExpr(vc, 2, 1);
  Expr twox = vc_multExpr(vc, two, x);
  Expr twox_plus_y = vc_plusExpr(vc, twox, y);

  Expr three = vc_ratExpr(vc, 3, 1);
  Expr twox_plus_y_geq_3 = vc_geExpr(vc, twox_plus_y, three);

  Expr formula = vc_impliesExpr(vc, vc_andExpr(vc, x_positive, y_positive),
                                twox_plus_y_geq_3);

  char* formulaString = vc_printExprString(vc, formula);

  printf("Checking validity of formula %s with CVC4.\n", formulaString);
  printf("CVC4 should return 1 (meaning VALID).\n");
  printf("Result from CVC4 is: %d\n", vc_query(vc, formula));

  free(formulaString);

  return 0;
}
