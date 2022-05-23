/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Test for project issue #425
 *
 */

#include <cassert>

#include "api/cpp/cvc5.h"

using namespace cvc5;

int main(void)
{
  Solver slv;
  slv.setOption("incremental", "false");
  slv.setOption("solve-int-as-bv", "5524936381719514648");
  Sort s1 = slv.getBooleanSort();
  Term t1 = slv.mkConst(s1, "_x0");
  Term t145 = slv.mkVar(s1, "_f11_0");
  Term t146 = slv.mkVar(s1, "_f11_1");
  Term t147 = slv.mkVar(s1, "_f11_2");
  Term t148 = slv.mkVar(s1, "_f11_3");
  Term t149 = slv.mkVar(s1, "_f11_4");
  Term t175 = slv.defineFun("_f11", {t145, t146, t147, t148, t149}, t1.getSort(), t1);
  slv.assertFormula({t1});
  (void) slv.simplify(t175);
}
