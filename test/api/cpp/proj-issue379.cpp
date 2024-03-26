/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #379.
 */
#include <cvc5/cvc5.h>

#include <cassert>

using namespace cvc5;

int main(void)
{
  TermManager tm;

  Sort bsort = tm.getBooleanSort();
  Sort psort = tm.mkParamSort("_x1");
  DatatypeConstructorDecl cdecl;
  DatatypeDecl dtdecl = tm.mkDatatypeDecl("x_0", {psort});
  cdecl = tm.mkDatatypeConstructorDecl("_x8");
  cdecl.addSelector("_x7", bsort);
  dtdecl.addConstructor(cdecl);
  cdecl = tm.mkDatatypeConstructorDecl("_x6");
  cdecl.addSelector("_x2", psort);
  cdecl.addSelectorSelf("_x3");
  cdecl.addSelector("_x4", psort);
  cdecl.addSelector("_x5", bsort);
  Sort s2 = tm.mkDatatypeSort(dtdecl);
  Sort s6 = s2.instantiate({bsort});
  Term t317 = tm.mkConst(bsort, "_x345");
  Term t843 = tm.mkConst(s6, "_x346");
  Term t879 = tm.mkTerm(Kind::APPLY_UPDATER,
                        {t843.getSort()
                             .getDatatype()
                             .getConstructor("_x8")
                             .getSelector("_x7")
                             .getUpdaterTerm(),
                         t843,
                         t317});
  assert(t879.getSort() == s6);
}
