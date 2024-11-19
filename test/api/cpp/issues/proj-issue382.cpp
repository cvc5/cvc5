/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mathias Preiner, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #382.
 */
#include <cvc5/cvc5.h>

using namespace cvc5;

int main(void)
{
  TermManager tm;
  Solver solver(tm);

  Sort s1 = tm.getBooleanSort();
  Sort psort = tm.mkParamSort("_x1");
  DatatypeConstructorDecl ctor = tm.mkDatatypeConstructorDecl("_x20");
  ctor.addSelector("_x19", psort);
  DatatypeDecl dtdecl = tm.mkDatatypeDecl("_x0", {psort});
  dtdecl.addConstructor(ctor);
  Sort s2 = tm.mkDatatypeSort(dtdecl);
  Sort s6 = s2.instantiate({s1});
  Term t13 = tm.mkVar(s6, "_x58");
  Term t18 = tm.mkConst(s6, "_x63");
  Term t52 = tm.mkVar(s6, "_x70");
  Term t53 = tm.mkTerm(Kind::MATCH_BIND_CASE,
                       {tm.mkTerm(Kind::VARIABLE_LIST, {t52}), t52, t18});
  Term t73 = tm.mkVar(s1, "_x78");
  Term t81 = tm.mkTerm(
      Kind::MATCH_BIND_CASE,
      {tm.mkTerm(Kind::VARIABLE_LIST, {t73}),
       tm.mkTerm(
           Kind::APPLY_CONSTRUCTOR,
           {s6.getDatatype().getConstructor("_x20").getInstantiatedTerm(s6),
            t73}),
       t18});
  Term t82 = tm.mkTerm(Kind::MATCH, {t13, t53, t53, t53, t81});
  Term t325 = tm.mkTerm(
      Kind::APPLY_SELECTOR,
      {t82.getSort().getDatatype().getSelector("_x19").getTerm(), t82});
  solver.simplify(t325);
}
