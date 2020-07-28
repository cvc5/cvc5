/*********************                                                        */
/*! \file theory_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Clark Barrett, Andres Noetzli, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::theory
 **
 ** Black box testing of CVC4::theory
 **/

#include <cxxtest/TestSuite.h>

//Used in some of the tests
#include <sstream>
#include <vector>

#include "api/cvc4cpp.h"
#include "expr/expr_manager.h"
#include "expr/node.h"
#include "expr/node_builder.h"
#include "expr/node_manager.h"
#include "expr/node_value.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/rewriter.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace std;
using namespace CVC4::theory;
using namespace CVC4::smt;

class TheoryBlack : public CxxTest::TestSuite {
 public:
  void setUp() override
  {
    d_slv = new api::Solver();
    d_em = d_slv->getExprManager();
    d_smt = d_slv->getSmtEngine();
    d_scope = new SmtScope(d_smt);
    // Ensure that the SMT engine is fully initialized (required for the
    // rewriter)
    d_smt->push();

    d_nm = NodeManager::fromExprManager(d_em);
  }

  void tearDown() override
  {
    delete d_scope;
    delete d_slv;
  }

  void testArrayConst() {
    TypeNode arrType = d_nm->mkArrayType(d_nm->integerType(), d_nm->integerType());
    Node zero = d_nm->mkConst(Rational(0));
    Node one = d_nm->mkConst(Rational(1));
    Node storeAll = d_nm->mkConst(ArrayStoreAll(arrType, zero));
    TS_ASSERT(storeAll.isConst());

    Node arr = d_nm->mkNode(STORE, storeAll, zero, zero);
    TS_ASSERT(!arr.isConst());
    arr = Rewriter::rewrite(arr);
    TS_ASSERT(arr.isConst());
    arr = d_nm->mkNode(STORE, storeAll, zero, one);
    TS_ASSERT(arr.isConst());
    Node arr2 = d_nm->mkNode(STORE, arr, one, zero);
    TS_ASSERT(!arr2.isConst());
    arr2 = Rewriter::rewrite(arr2);
    TS_ASSERT(arr2.isConst());
    arr2 = d_nm->mkNode(STORE, arr, one, one);
    TS_ASSERT(arr2.isConst());
    arr2 = d_nm->mkNode(STORE, arr, zero, one);
    TS_ASSERT(!arr2.isConst());
    arr2 = Rewriter::rewrite(arr2);
    TS_ASSERT(arr2.isConst());

    arrType = d_nm->mkArrayType(d_nm->mkBitVectorType(1), d_nm->mkBitVectorType(1));
    zero = d_nm->mkConst(BitVector(1,unsigned(0)));
    one = d_nm->mkConst(BitVector(1,unsigned(1)));
    storeAll = d_nm->mkConst(ArrayStoreAll(arrType, zero));
    TS_ASSERT(storeAll.isConst());

    arr = d_nm->mkNode(STORE, storeAll, zero, zero);
    TS_ASSERT(!arr.isConst());
    arr = Rewriter::rewrite(arr);
    TS_ASSERT(arr.isConst());
    arr = d_nm->mkNode(STORE, storeAll, zero, one);
    arr = Rewriter::rewrite(arr); 
    TS_ASSERT(arr.isConst());
    arr2 = d_nm->mkNode(STORE, arr, one, zero);
    TS_ASSERT(!arr2.isConst());
    arr2 = Rewriter::rewrite(arr2);
    TS_ASSERT(arr2.isConst());
    arr2 = d_nm->mkNode(STORE, arr, one, one);
    TS_ASSERT(!arr2.isConst());
    arr2 = Rewriter::rewrite(arr2);
    TS_ASSERT(arr2.isConst());
    arr2 = d_nm->mkNode(STORE, arr, zero, one);
    TS_ASSERT(!arr2.isConst());
    arr2 = Rewriter::rewrite(arr2);
    TS_ASSERT(arr2.isConst());

    arrType = d_nm->mkArrayType(d_nm->mkBitVectorType(2), d_nm->mkBitVectorType(2));
    zero = d_nm->mkConst(BitVector(2,unsigned(0)));
    one = d_nm->mkConst(BitVector(2,unsigned(1)));
    Node two = d_nm->mkConst(BitVector(2,unsigned(2)));
    Node three = d_nm->mkConst(BitVector(2,unsigned(3)));
    storeAll = d_nm->mkConst(ArrayStoreAll(arrType, one));
    TS_ASSERT(storeAll.isConst());

    arr = d_nm->mkNode(STORE, storeAll, zero, zero);
    TS_ASSERT(arr.isConst());
    arr2 = d_nm->mkNode(STORE, arr, one, zero);
    TS_ASSERT(!arr2.isConst());
    arr2 = Rewriter::rewrite(arr2);
    TS_ASSERT(arr2.isConst());

    arr = d_nm->mkNode(STORE, storeAll, one, three);
    TS_ASSERT(arr.isConst());
    arr2 = d_nm->mkNode(STORE, arr, one, one);
    TS_ASSERT(!arr2.isConst());
    arr2 = Rewriter::rewrite(arr2);
    TS_ASSERT(arr2 == storeAll);

    arr2 = d_nm->mkNode(STORE, arr, zero, zero);
    TS_ASSERT(!arr2.isConst());
    TS_ASSERT(Rewriter::rewrite(arr2).isConst());
    arr2 = d_nm->mkNode(STORE, arr2, two, two);
    TS_ASSERT(!arr2.isConst());
    TS_ASSERT(Rewriter::rewrite(arr2).isConst());
    arr2 = d_nm->mkNode(STORE, arr2, three, one);
    TS_ASSERT(!arr2.isConst());
    TS_ASSERT(Rewriter::rewrite(arr2).isConst());
    arr2 = d_nm->mkNode(STORE, arr2, three, three);
    TS_ASSERT(!arr2.isConst());
    TS_ASSERT(Rewriter::rewrite(arr2).isConst());
    arr2 = d_nm->mkNode(STORE, arr2, two, zero);
    TS_ASSERT(!arr2.isConst());
    arr2 = Rewriter::rewrite(arr2);
    TS_ASSERT(arr2.isConst());

  }

 private:
  api::Solver* d_slv;
  ExprManager* d_em;
  SmtEngine* d_smt;
  NodeManager* d_nm;
  SmtScope* d_scope;
};
