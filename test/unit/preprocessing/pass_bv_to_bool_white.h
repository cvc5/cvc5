/*********************                                                        */
/*! \file pass_bv_to_bool_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Unit tests for bv-to-bool preprocessing pass.
 **
 ** Unit tests for bv-to-bool preprocessing pass.
 **/

#include "expr/node.h"
#include "expr/node_manager.h"
#include "preprocessing/passes/bv_to_bool.cpp"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/rewriter.h"
#include "util/bitvector.h"

#include <cxxtest/TestSuite.h>
#include <iostream>
#include <vector>

using namespace CVC4;
using namespace CVC4::preprocessing;
using namespace CVC4::theory;
using namespace CVC4::smt;

class BVToBoolWhite : public CxxTest::TestSuite
{
  ExprManager* d_em;
  NodeManager* d_nm;
  SmtEngine *d_smt;
  SmtScope *d_scope;
  Node d_unaryOne;
  Node d_two;
  Node d_three;

 public:
  BVToBoolWhite() {}

  void setUp() override
  {
    d_em = new ExprManager();
    d_nm = NodeManager::fromExprManager(d_em);
    d_smt = new SmtEngine(d_em);
    d_scope = new SmtScope(d_smt);
    d_unaryOne = d_nm->mkConst<BitVector>(BitVector(1, 1u));
    d_two = d_nm->mkConst<BitVector>(BitVector(16, 2u));
    d_three = d_nm->mkConst<BitVector>(BitVector(16, 3u));
  }

  void tearDown() override
  {
    (void)d_scope;
    d_unaryOne = Node::null();
    d_two = Node::null();
    d_three = Node::null();
    delete d_scope;
    delete d_smt;
    delete d_em;
  }

  // Test wehther BITVECTOR_ITE is correctly eliminated.
  // bvite(1, 2, 3) should get rewritten to ite(true, 2, 3)
  void testLiftBVIte()
  {
    Node bvite = d_nm->mkNode(kind::BITVECTOR_ITE, d_unaryOne, d_two, d_three);
    Node ite = d_nm->mkNode(kind::ITE, d_nm->mkConst<bool>(true), d_two, d_three);

    passes::BVToBool bvtobool(nullptr);
    AssertionPipeline apipe;
    apipe.push_back(bvite);
    PreprocessingPassResult pres = bvtobool.applyInternal(&apipe);

    TS_ASSERT(pres == PreprocessingPassResult::NO_CONFLICT);
    TS_ASSERT_EQUALS(apipe[0], Rewriter::rewrite(ite));
  }
};
