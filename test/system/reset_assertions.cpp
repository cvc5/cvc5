/*********************                                                        */
/*! \file reset_assertions.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A simple test for SmtEngine::resetAssertions()
 **
 ** This program indirectly also tests some corner cases w.r.t.
 ** context-dependent datastructures: resetAssertions() pops the contexts to
 ** zero but some context-dependent datastructures are created at leevel 1,
 ** which the datastructure needs to handle properly problematic.
 **/

#include <iostream>
#include <sstream>

#include "expr/expr.h"
#include "smt/smt_engine.h"

using namespace CVC4;

int main()
{
  ExprManager em;
  SmtEngine smt(&em);

  smt.setOption("incremental", SExpr(true));

  Type real = em.realType();
  Expr x = em.mkVar("x", real);
  Expr four = em.mkConst(Rational(4));
  Expr xEqFour = em.mkExpr(Kind::EQUAL, x, four);
  smt.assertFormula(xEqFour);
  std::cout << smt.checkSat() << std::endl;

  smt.resetAssertions();

  Type elementType = em.integerType();
  Type indexType = em.integerType();
  Type arrayType = em.mkArrayType(indexType, elementType);
  Expr array = em.mkVar("array", arrayType);
  Expr arrayAtFour = em.mkExpr(Kind::SELECT, array, four);
  Expr ten = em.mkConst(Rational(10));
  Expr arrayAtFour_eq_ten = em.mkExpr(Kind::EQUAL, arrayAtFour, ten);
  smt.assertFormula(arrayAtFour_eq_ten);
  std::cout << smt.checkSat() << std::endl;
}
