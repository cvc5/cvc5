/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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
  TermManager tm;
  Sort s1 = tm.mkUninterpretedSort("_u0");
  Sort s2 = tm.getStringSort();
  Sort _p2 = tm.mkParamSort("_p2");
  Sort _p3 = tm.mkParamSort("_p3");
  DatatypeDecl _dt1 = tm.mkDatatypeDecl("_dt1", {_p2, _p3});
  DatatypeConstructorDecl _cons21 = tm.mkDatatypeConstructorDecl("_cons21");
  _cons21.addSelector("_sel16", _p2);
  _dt1.addConstructor(_cons21);
  Sort s3 = tm.mkDatatypeSort(_dt1);
  Sort s4 = tm.mkBagSort(s2);
  Sort s5 = tm.mkArraySort(s1, s4);
  Sort s9 = s3.instantiate({s4, s4});
  (void)s5.substitute({s4}, {s9});
}
