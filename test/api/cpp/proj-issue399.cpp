/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #399
 *
 */

#include <cvc5/cvc5.h>

#include <cassert>

using namespace cvc5;

int main(void)
{
  Solver slv;
  Sort s1 = slv.mkUninterpretedSort("_u0");
  Sort s2 = slv.getStringSort();
  Sort _p2 = slv.mkParamSort("_p2");
  Sort _p3 = slv.mkParamSort("_p3");
  DatatypeDecl _dt1 = slv.mkDatatypeDecl("_dt1", {_p2, _p3});
  DatatypeConstructorDecl _cons21 = slv.mkDatatypeConstructorDecl("_cons21");
  _cons21.addSelector("_sel16", _p2);
  _dt1.addConstructor(_cons21);
  Sort s3 = slv.mkDatatypeSort(_dt1);
  Sort s4 = slv.mkBagSort(s2);
  Sort s5 = slv.mkArraySort(s1, s4);
  Sort s9 = s3.instantiate({s4, s4});
  (void)s5.substitute({s4}, {s9});
}
