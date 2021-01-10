/*********************                                                        */
/*! \file pass_foreign_theory_rewrite.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Mathias Preiner, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Unit tests for Foreign Theory Rerwrite prepricessing pass
 ** Unit tests for Foreign Theory Rerwrite prepricessing pass
 **/

#include <cxxtest/TestSuite.h>

#include "expr/node_manager.h"
#include "preprocessing/passes/foreign_theory_rewrite.h"
#include "smt/smt_engine.h"
#include "test_utils.h"

using namespace CVC4;
using namespace CVC4::preprocessing::passes;

class ForeignTheoryRewriteWhite : public CxxTest::TestSuite
{
 public:
  ForeignTheoryRewriteWhite() {}

  void setUp() override
  {
    d_em = new ExprManager();
    d_nm = NodeManager::fromExprManager(d_em);
    d_smt = new SmtEngine(d_nm);
    d_smt->finishInit();
  }

  void tearDown() override
  {
    delete d_smt;
    delete d_em;
  }

  void testSimplify()
  {
    std::cout << "len(x) >= 0 is simplified to true" << std::endl;
    Node x = d_nm->mkVar("x", d_nm->stringType());
    Node len_x = d_nm->mkNode(kind::STRING_LENGTH, x);
    Node zero = d_nm->mkConst<Rational>(0);
    Node geq1 = d_nm->mkNode(kind::GEQ, len_x, zero);
    Node tt = d_nm->mkConst<bool>(true);
    Node simplified1 = ForeignTheoryRewrite::foreignRewrite(geq1);
    TS_ASSERT_EQUALS(simplified1, tt);

    std::cout << "len(x) >= n is not simplified to true" << std::endl;
    Node n = d_nm->mkVar("n", d_nm->integerType());
    Node geq2 = d_nm->mkNode(kind::GEQ, len_x, n);
    Node simplified2 = ForeignTheoryRewrite::foreignRewrite(geq2);
    TS_ASSERT(simplified2 != tt);
  }

 private:
  ExprManager* d_em;
  NodeManager* d_nm;
  SmtEngine* d_smt;
};
