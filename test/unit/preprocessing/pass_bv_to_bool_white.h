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

#include "context/context.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "preprocessing/passes/bv_to_bool.cpp"
#include "preprocessing/preprocessing_pass.h"
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
  ExprManager *d_em;
  NodeManager *d_nm;
  SmtEngine *d_smt;
  SmtScope *d_scope;
  Node d_zero;
  Node d_one;
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

    d_zero = bv::utils::mkZero(16);
    d_one = d_nm->mkConst<BitVector>(BitVector(16, 1u));
    d_two = d_nm->mkConst<BitVector>(BitVector(16, 2u));
    d_three = d_nm->mkConst<BitVector>(BitVector(16, 3u));
  }

  void tearDown() override
  {
    (void)d_scope;
    d_zero = Node::null();
    d_one = Node::null();
    d_two = Node::null();
    d_three = Node::null();
    delete d_scope;
    delete d_smt;
    delete d_em;
  }

  void testBvToBool()
  {
    Node bvite = d_nm->mkNode(kind::BITVECTOR_ITE, d_unaryOne, two, three);
    Node ite = d_nm->mkNode(kind::ITE, nm->mkConst<Boolean>(true), two, three);
    
    passes::BVToBool bvtobool(nullptr);
    AssertionPipeline apipe;
    apipe.push_back(bvite);
    PreprocessingPassResult pres = bvtobool.applyInternal(&apipe);
    
    TS_ASSERT (pres == PreprocessingPassResult::NO_CONFLICT);
    TS_ASSERT_EQUAL(apipe[0], ite);
  }
};
