/*********************                                                        */
/*! \file array_store_all_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Morgan Deters, Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
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
#include "expr/type.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "test_utils.h"

using namespace CVC4;
using namespace std;

class ArrayStoreAllWhite : public CxxTest::TestSuite
{
 public:
  void setUp() override
  {
    d_slv = new api::Solver();
    d_scope = new smt::SmtScope(d_slv->getSmtEngine());
    d_nm = d_slv->getSmtEngine()->d_nodeManager;
  }

  void tearDown() override
  {
    delete d_scope;
    delete d_slv;
  }

  void testStoreAll()
  {
    TypeNode usort = d_nm->mkSort("U");
    ArrayStoreAll(d_nm->mkArrayType(d_nm->integerType(), d_nm->realType()),
                  d_nm->mkConst(Rational(9, 2)));
    ArrayStoreAll(d_nm->mkArrayType(d_nm->mkSort("U"), usort),
                  d_nm->mkConst(UninterpretedConstant(usort, 0)));
    ArrayStoreAll(d_nm->mkArrayType(d_nm->mkBitVectorType(8), d_nm->realType()),
                  d_nm->mkConst(Rational(0)));
    ArrayStoreAll(
        d_nm->mkArrayType(d_nm->mkBitVectorType(8), d_nm->integerType()),
        d_nm->mkConst(Rational(0)));
  }

  void testTypeErrors()
  {
    TS_ASSERT_THROWS(ArrayStoreAll(d_nm->integerType(),
                                   d_nm->mkConst(UninterpretedConstant(
                                       d_nm->mkSort("U"), 0))),
                     IllegalArgumentException&);
    TS_ASSERT_THROWS(
        ArrayStoreAll(d_nm->integerType(), d_nm->mkConst(Rational(9, 2))),
        IllegalArgumentException&);
    TS_ASSERT_THROWS(
        ArrayStoreAll(d_nm->mkArrayType(d_nm->integerType(), d_nm->mkSort("U")),
                      d_nm->mkConst(Rational(9, 2))),
        IllegalArgumentException&);
  }

  void testConstError()
  {
    TypeNode usort = d_nm->mkSort("U");
    TS_ASSERT_THROWS_ANYTHING(ArrayStoreAll(
        d_nm->mkArrayType(d_nm->mkSort("U"), usort), d_nm->mkVar(usort)));
    TS_ASSERT_THROWS_ANYTHING(ArrayStoreAll(
        d_nm->integerType(), d_nm->mkVar("x", d_nm->integerType())));
    TS_ASSERT_THROWS_ANYTHING(
        ArrayStoreAll(d_nm->integerType(),
                      d_nm->mkNode(kind::PLUS,
                                   d_nm->mkConst(Rational(1)),
                                   d_nm->mkConst(Rational(0)))));
  }

 private:
  api::Solver* d_slv;
  smt::SmtScope* d_scope;
  NodeManager* d_nm;
}; /* class ArrayStoreAllBlack */
