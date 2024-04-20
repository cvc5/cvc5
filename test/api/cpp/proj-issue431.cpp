/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #431.
 */
#include <cvc5/cvc5.h>

#include <cassert>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver solver(tm);

  solver.setOption("produce-abducts", "true");
  Sort s2 = tm.mkBitVectorSort(22);
  Sort s4 = tm.mkSetSort(s2);
  Sort s5 = tm.getBooleanSort();
  Sort s6 = tm.getRealSort();
  Sort s7 = tm.mkFunctionSort({s6}, s5);
  DatatypeDecl _dt46 = tm.mkDatatypeDecl("_dt46", {});
  DatatypeConstructorDecl _cons64 = tm.mkDatatypeConstructorDecl("_cons64");
  _cons64.addSelector("_sel62", s6);
  _cons64.addSelector("_sel63", s4);
  _dt46.addConstructor(_cons64);
  Sort s14 = tm.mkDatatypeSorts({_dt46})[0];
  Term t31 = tm.mkConst(s7, "_x100");
  Term t47 = tm.mkConst(s14, "_x112");
  Term sel = t47.getSort()
                 .getDatatype()
                 .getConstructor("_cons64")
                 .getSelector("_sel62")
                 .getTerm();
  Term t274 = tm.mkTerm(Kind::APPLY_SELECTOR, {sel, t47});
  Term t488 = tm.mkTerm(Kind::APPLY_UF, {t31, t274});
  solver.assertFormula({t488});
  Term abduct;
  abduct = solver.getAbduct(t488);
}
