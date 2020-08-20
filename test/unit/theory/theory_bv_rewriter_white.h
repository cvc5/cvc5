/*********************                                                        */
/*! \file theory_bv_rewriter_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Unit tests for the bit-vector rewriter
 **
 ** Unit tests for the bit-vector rewriter.
 **/

#include "expr/node.h"
#include "expr/node_manager.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/rewriter.h"
#include "util/bitvector.h"

#include <cxxtest/TestSuite.h>
#include <iostream>
#include <memory>
#include <vector>

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::smt;
using namespace CVC4::theory;

class TheoryBvRewriterWhite : public CxxTest::TestSuite
{
 public:
  TheoryBvRewriterWhite() {}

  void setUp() override
  {
    Options opts;
    opts.setOutputLanguage(language::output::LANG_SMTLIB_V2);
    d_em = new ExprManager;
    d_smt = new SmtEngine(d_em, &opts);
    d_scope = new SmtScope(d_smt);
    d_smt->finishInit();

    d_nm = NodeManager::currentNM();
  }

  void tearDown() override
  {
    delete d_scope;
    delete d_smt;
    delete d_em;
  }

  Node boolToBv(Node b)
  {
    return d_nm->mkNode(ITE,
                        b,
                        d_nm->mkConst(BitVector(1, 1u)),
                        d_nm->mkConst(BitVector(1, 0u)));
  }

  void testRewriteToFixpoint()
  {
    TypeNode boolType = d_nm->booleanType();
    TypeNode bvType = d_nm->mkBitVectorType(1);

    Node zero = d_nm->mkConst(BitVector(1, 0u));
    Node b1 = d_nm->mkVar("b1", boolType);
    Node b2 = d_nm->mkVar("b2", boolType);
    Node b3 = d_nm->mkVar("b3", boolType);
    Node bv = d_nm->mkVar("bv", bvType);

    Node n = d_nm->mkNode(
        BITVECTOR_ITE,
        boolToBv(b1),
        d_nm->mkNode(BITVECTOR_ITE,
                     boolToBv(b2),
                     d_nm->mkNode(BITVECTOR_ITE, boolToBv(b3), zero, bv),
                     bv),
        bv);
    Node nr = Rewriter::rewrite(n);
    TS_ASSERT_EQUALS(nr, Rewriter::rewrite(nr));
  }

  void testRewriteBvIte()
  {
    TypeNode boolType = d_nm->booleanType();
    TypeNode bvType = d_nm->mkBitVectorType(1);

    Node zero = d_nm->mkConst(BitVector(1, 0u));
    Node c1 = d_nm->mkVar("c1", bvType);
    Node c2 = d_nm->mkVar("c2", bvType);

    Node ite = d_nm->mkNode(BITVECTOR_ITE, c2, zero, zero);
    Node n = d_nm->mkNode(BITVECTOR_ITE, c1, ite, ite);
    Node nr = Rewriter::rewrite(n);
    TS_ASSERT_EQUALS(nr, Rewriter::rewrite(nr));
  }

 private:
  ExprManager* d_em;
  SmtEngine* d_smt;
  SmtScope* d_scope;

  NodeManager* d_nm;
};
