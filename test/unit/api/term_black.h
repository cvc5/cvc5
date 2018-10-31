/*********************                                                        */
/*! \file term_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of the Term class
 **/

#include <cxxtest/TestSuite.h>

#include "api/cvc4cpp.h"

using namespace CVC4::api;

class TermBlack : public CxxTest::TestSuite
{
 public:
  void setUp() override {}
  void tearDown() override {}

  void testTermAssignment()
  {
    Term t1 = d_solver.mkReal(1);
    Term t2 = t1;
    t2 = d_solver.mkReal(2);
    TS_ASSERT_EQUALS(t1, d_solver.mkReal(1));
  }

 private:
  Solver d_solver;
};
