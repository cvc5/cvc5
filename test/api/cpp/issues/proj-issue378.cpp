/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #378.
 */
#include <cvc5/cvc5.h>

#include <cassert>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver solver(tm);

  DatatypeDecl dtdecl;
  DatatypeConstructorDecl cdecl;

  Sort s1 = tm.getBooleanSort();

  dtdecl = tm.mkDatatypeDecl("_x0");
  cdecl = tm.mkDatatypeConstructorDecl("_x6");
  cdecl.addSelector("_x1", s1);
  dtdecl.addConstructor(cdecl);
  Sort s2 = tm.mkDatatypeSort(dtdecl);

  dtdecl = tm.mkDatatypeDecl("_x36");
  cdecl = tm.mkDatatypeConstructorDecl("_x42");
  cdecl.addSelector("_x37", s1);
  dtdecl.addConstructor(cdecl);
  Sort s4 = tm.mkDatatypeSort(dtdecl);

  Term t1 = tm.mkConst(s1, "_x53");
  Term t4 = tm.mkConst(s4, "_x56");
  Term t7 = tm.mkConst(s2, "_x58");

  Sort sp = tm.mkParamSort("_x178");
  dtdecl = tm.mkDatatypeDecl("_x176", {sp});
  cdecl = tm.mkDatatypeConstructorDecl("_x184");
  cdecl.addSelector("_x180", s2);
  dtdecl.addConstructor(cdecl);
  cdecl = tm.mkDatatypeConstructorDecl("_x186");
  cdecl.addSelector("_x185", sp);
  dtdecl.addConstructor(cdecl);
  Sort s7 = tm.mkDatatypeSort(dtdecl);
  Sort s9 = s7.instantiate({s2});
  Term t1507 =
      tm.mkTerm(Kind::APPLY_CONSTRUCTOR,
                {s9.getDatatype().getConstructor("_x184").getTerm(), t7});
  (void)tm.mkTerm(
      Kind::APPLY_UPDATER,
      {s9.getDatatype().getConstructor("_x186").getSelector("_x185").getTerm(),
       t1507,
       t7});
}
