/*********************                                                        */
/*! \file array_store_all_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::ArrayStoreAll
 **
 ** Black box testing of CVC4::ArrayStoreAll.
 **/

#include <cxxtest/TestSuite.h>

#include "api/cvc4cpp.h"
#include "expr/array_store_all.h"
#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "expr/expr_manager_scope.h"
#include "expr/type.h"
#include "test_utils.h"

using namespace CVC4;
using namespace std;

class ArrayStoreAllBlack : public CxxTest::TestSuite {
 public:
  void setUp() override
  {
    d_slv = new api::Solver();
    d_em = d_slv->getExprManager();
  }

  void tearDown() override { delete d_slv; }

  void testStoreAll() {
    Type usort = d_em->mkSort("U");
    ArrayStoreAll(d_em->mkArrayType(d_em->integerType(), d_em->realType()),
                  d_em->mkConst(Rational(9, 2)));
    ArrayStoreAll(d_em->mkArrayType(d_em->mkSort("U"), usort),
                  d_em->mkConst(UninterpretedConstant(usort, 0)));
    ArrayStoreAll(d_em->mkArrayType(d_em->mkBitVectorType(8), d_em->realType()),
                  d_em->mkConst(Rational(0)));
    ArrayStoreAll(
        d_em->mkArrayType(d_em->mkBitVectorType(8), d_em->integerType()),
        d_em->mkConst(Rational(0)));
  }

  void testTypeErrors()
  {
    TS_ASSERT_THROWS(ArrayStoreAll(d_em->integerType(),
                                   d_em->mkConst(UninterpretedConstant(
                                       d_em->mkSort("U"), 0))),
                     IllegalArgumentException&);
    TS_ASSERT_THROWS(
        ArrayStoreAll(d_em->integerType(), d_em->mkConst(Rational(9, 2))),
        IllegalArgumentException&);
    TS_ASSERT_THROWS(
        ArrayStoreAll(d_em->mkArrayType(d_em->integerType(), d_em->mkSort("U")),
                      d_em->mkConst(Rational(9, 2))),
        IllegalArgumentException&);
  }

  void testConstError() {
    Type usort = d_em->mkSort("U");
    TS_ASSERT_THROWS_ANYTHING(ArrayStoreAll(
        d_em->mkArrayType(d_em->mkSort("U"), usort), d_em->mkVar(usort)));
    TS_ASSERT_THROWS_ANYTHING(ArrayStoreAll(
        d_em->integerType(), d_em->mkVar("x", d_em->integerType())));
    TS_ASSERT_THROWS_ANYTHING(
        ArrayStoreAll(d_em->integerType(),
                      d_em->mkExpr(kind::PLUS, d_em->mkConst(Rational(1)),
                                   d_em->mkConst(Rational(0)))));
  }

 private:
  api::Solver* d_slv;
  ExprManager* d_em;
}; /* class ArrayStoreAllBlack */
