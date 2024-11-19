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
 * Test for project issue #386.
 */
#include <cvc5/cvc5.h>

#include <cassert>

using namespace cvc5;

int main(void)
{
  TermManager tm;

  Sort s1 = tm.getBooleanSort();
  Sort p1 = tm.mkParamSort("_p1");
  Sort p2 = tm.mkParamSort("_p2");
  DatatypeDecl dtdecl = tm.mkDatatypeDecl("_x0", {p1, p2});
  DatatypeConstructorDecl ctordecl = tm.mkDatatypeConstructorDecl("_x1");
  ctordecl.addSelector("_x2", p1);
  dtdecl.addConstructor(ctordecl);
  Sort s2 = tm.mkDatatypeSort(dtdecl);
  try
  {
    s2.instantiate({s1});
  }
  catch (CVC5ApiException& e)
  {
    return 0;
  }
  assert(false);
}
