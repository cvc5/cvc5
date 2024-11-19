/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #373.
 */
#include <cvc5/cvc5.h>

#include <cassert>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver solver(tm);

  Sort s1 = tm.getRealSort();
  DatatypeConstructorDecl ctor13 = tm.mkDatatypeConstructorDecl("_x115");
  ctor13.addSelector("_x109", s1);
  Sort s4 = solver.declareDatatype("_x86", {ctor13});
  Term t452 = tm.mkVar(s1, "_x281");
  Term bvl = tm.mkTerm(tm.mkOp(Kind::VARIABLE_LIST), {t452});
  Term acons =
      tm.mkTerm(tm.mkOp(Kind::APPLY_CONSTRUCTOR),
                {s4.getDatatype().getConstructor("_x115").getTerm(), t452});
  // we expect a type exception
  try
  {
    tm.mkTerm(tm.mkOp(Kind::APPLY_CONSTRUCTOR), {bvl, acons, t452});
  }
  catch (CVC5ApiException& e)
  {
    return 0;
  }
  assert(false);
}
