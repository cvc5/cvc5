/*********************                                                        */
/*! \file array_store_all_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::ArrayStoreAll
 **
 ** Black box testing of CVC4::ArrayStoreAll.
 **/

#include <cxxtest/TestSuite.h>

#include "expr/array_store_all.h"
#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "expr/expr_manager_scope.h"
#include "expr/type.h"

using namespace CVC4;
using namespace std;

class ArrayStoreAllBlack : public CxxTest::TestSuite {
  ExprManager* d_em;
  ExprManagerScope* d_scope;

 public:
  void setUp() {
    d_em = new ExprManager();
    d_scope = new ExprManagerScope(*d_em);
  }

  void tearDown() {
    delete d_scope;
    delete d_em;
  }

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

  void testTypeErrors() {
    // these two throw an AssertionException in assertions-enabled builds, and
    // an IllegalArgumentException in production builds
    TS_ASSERT_THROWS_ANYTHING(ArrayStoreAll(
        d_em->integerType(),
        d_em->mkConst(UninterpretedConstant(d_em->mkSort("U"), 0))));
    TS_ASSERT_THROWS_ANYTHING(
        ArrayStoreAll(d_em->integerType(), d_em->mkConst(Rational(9, 2))));

    TS_ASSERT_THROWS(
        ArrayStoreAll(d_em->mkArrayType(d_em->integerType(), d_em->mkSort("U")),
                      d_em->mkConst(Rational(9, 2))),
        IllegalArgumentException);
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

}; /* class ArrayStoreAllBlack */
