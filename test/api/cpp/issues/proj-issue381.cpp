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
 * Test for project issue #381.
 */
#include <cvc5/cvc5.h>

#include <cassert>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver solver(tm);

  Sort s1 = tm.getBooleanSort();
  Sort psort = tm.mkParamSort("_x9");
  DatatypeDecl dtdecl = tm.mkDatatypeDecl("_x8", {psort});
  DatatypeConstructorDecl ctor = tm.mkDatatypeConstructorDecl("_x22");
  ctor.addSelector("_x19", s1);
  dtdecl.addConstructor(ctor);
  Sort s3 = tm.mkDatatypeSort(dtdecl);
  Sort s6 = s3.instantiate({s1});
  Term t26 = tm.mkConst(s6, "_x63");
  Term t5 = tm.mkTrue();
  Term t187 = tm.mkTerm(Kind::APPLY_UPDATER,
                        {t26.getSort()
                             .getDatatype()
                             .getConstructor("_x22")
                             .getSelector("_x19")
                             .getUpdaterTerm(),
                         t26,
                         t5});
  (void)solver.simplify(t187);
}
