/*********************                                                        */
/*! \file theory_sets_type_rules_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief White box testing of sets typing rules
 **/

#include <cxxtest/TestSuite.h>

#include "api/cvc4cpp.h"
#include "expr/dtype.h"
#include "smt/smt_engine.h"

using namespace CVC4;
using namespace CVC4::api;

class SetsTypeRuleWhite : public CxxTest::TestSuite
{
 public:
  void setUp() override
  {
    d_slv.reset(new Solver());
    d_em.reset(new ExprManager());
    d_smt.reset(new SmtEngine(d_em.get()));
    d_nm.reset(NodeManager::fromExprManager(d_em.get()));
    d_smt->finishInit();
  }

  void tearDown() override
  {
    d_slv.reset();
    d_smt.reset();
    d_nm.release();
    d_em.reset();
  }

  void testIsisComparableTo()
  {
    TypeNode setRealType = d_nm->mkSetType(d_nm->realType());
    TypeNode setIntType = d_nm->mkSetType(d_nm->integerType());
    TS_ASSERT(!setIntType.isComparableTo(setRealType));
    TS_ASSERT(!setIntType.isSubtypeOf(setRealType));
    TS_ASSERT(!setRealType.isComparableTo(setIntType));
    TS_ASSERT(!setRealType.isComparableTo(setIntType));
  }

  void testSingletonTerm()
  {
    Sort realSort = d_slv->getRealSort();
    Sort intSort = d_slv->getIntegerSort();
    Term emptyReal = d_slv->mkEmptySet(d_slv->mkSetSort(realSort));
    Term integerOne = d_slv->mkInteger(1);
    Term realOne = d_slv->mkReal(1);
    Term singletonInt = d_slv->mkTerm(api::SINGLETON, integerOne);
    Term singletonReal = d_slv->mkTerm(api::SINGLETON, realOne);
    // (union
    //    (singleton (singleton_op Int) 1)
    //    (as emptyset (Set Real)))
    TS_ASSERT_THROWS(d_slv->mkTerm(UNION, singletonInt, emptyReal),
                     CVC4ApiException);
    // (union
    //    (singleton (singleton_op Real) 1)
    //    (as emptyset (Set Real)))
    TS_ASSERT_THROWS_NOTHING(d_slv->mkTerm(UNION, singletonReal, emptyReal));
  }

  void testSingletonNode()
  {
    Node singletonInt = d_nm->mkConst(SingletonOp(d_nm->integerType()));
    Node singletonReal = d_nm->mkConst(SingletonOp(d_nm->realType()));
    Node intConstant = d_nm->mkConst(Rational(1));
    Node realConstant = d_nm->mkConst(Rational(1, 5));
    // (singleton (singleton_op Real) 1)
    TS_ASSERT_THROWS_NOTHING(
        d_nm->mkSingleton(d_nm->realType(), intConstant));
    // (singleton (singleton_op Int) (/ 1 5))
    // This fails now with the assertions. cxxtest does not catch that.
    // TS_ASSERT_THROWS(d_nm->mkSingleton(d_nm->integerType(), realConstant),
    //                 Exception);

    Node n = d_nm->mkSingleton(d_nm->realType(), intConstant);
    // the type of (singleton (singleton_op Real) 1) is (Set Real)
    TS_ASSERT(n.getType() == d_nm->mkSetType(d_nm->realType()));
    // (singleton (singleton_op Real) 1) is a constant in normal form
    TS_ASSERT(n.isConst());
  }

 private:
  std::unique_ptr<Solver> d_slv;
  std::unique_ptr<ExprManager> d_em;
  std::unique_ptr<SmtEngine> d_smt;
  std::unique_ptr<NodeManager> d_nm;
}; /* class SetsTypeRuleWhite */
