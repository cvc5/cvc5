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

#include "api/cvc4cpp.h"

using namespace CVC4::api;

int main()
{
  Solver slv;
  slv.setOption("incremental", "true");

  Sort real = slv.getRealSort();
  Term x = slv.mkConst(real, "x");
  Term four = slv.mkReal(4);
  Term xEqFour = slv.mkTerm(Kind::EQUAL, x, four);
  slv.assertFormula(xEqFour);
  std::cout << slv.checkSat() << std::endl;

  slv.resetAssertions();

  Sort elementType = slv.getIntegerSort();
  Sort indexType = slv.getIntegerSort();
  Sort arrayType = slv.mkArraySort(indexType, elementType);
  Term array = slv.mkConst(arrayType, "array");
  Term arrayAtFour = slv.mkTerm(Kind::SELECT, array, four);
  Term ten = slv.mkReal(10);
  Term arrayAtFour_eq_ten = slv.mkTerm(Kind::EQUAL, arrayAtFour, ten);
  slv.assertFormula(arrayAtFour_eq_ten);
  std::cout << slv.checkSat() << std::endl;
}
