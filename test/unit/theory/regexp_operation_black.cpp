/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Unit tests for symbolic regular expression operations.
 */

#include <iostream>
#include <memory>
#include <vector>

#include "api/cpp/cvc5.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "smt/smt_engine_scope.h"
#include "test_smt.h"
#include "theory/rewriter.h"
#include "theory/strings/regexp_operation.h"
#include "theory/strings/skolem_cache.h"

namespace cvc5 {

using namespace kind;
using namespace theory;
using namespace theory::strings;

namespace test {

class TestTheoryBlackRegexpOperation : public TestSmt
{
 protected:
  void SetUp() override
  {
    TestSmt::SetUp();
    d_skolemCache.reset(new SkolemCache());
    d_regExpOpr.reset(new RegExpOpr(d_skolemCache.get()));
  }

  void includes(Node r1, Node r2)
  {
    r1 = Rewriter::rewrite(r1);
    r2 = Rewriter::rewrite(r2);
    std::cout << r1 << " includes " << r2 << std::endl;
    ASSERT_TRUE(d_regExpOpr->regExpIncludes(r1, r2));
  }

  void doesNotInclude(Node r1, Node r2)
  {
    r1 = Rewriter::rewrite(r1);
    r2 = Rewriter::rewrite(r2);
    std::cout << r1 << " does not include " << r2 << std::endl;
    ASSERT_FALSE(d_regExpOpr->regExpIncludes(r1, r2));
  }

  std::unique_ptr<SkolemCache> d_skolemCache;
  std::unique_ptr<RegExpOpr> d_regExpOpr;
};

TEST_F(TestTheoryBlackRegexpOperation, basic)
{
  Node sigma = d_nodeManager->mkNode(REGEXP_SIGMA);
  Node sigmaStar = d_nodeManager->mkNode(REGEXP_STAR, sigma);
  Node a = d_nodeManager->mkNode(STRING_TO_REGEXP,
                                 d_nodeManager->mkConst(String("a")));
  Node c = d_nodeManager->mkNode(STRING_TO_REGEXP,
                                 d_nodeManager->mkConst(String("c")));
  Node abc = d_nodeManager->mkNode(STRING_TO_REGEXP,
                                   d_nodeManager->mkConst(String("abc")));
  Node sigma3 = d_nodeManager->mkNode(REGEXP_CONCAT, sigma, sigma, sigma);
  Node asc = d_nodeManager->mkNode(REGEXP_CONCAT, a, sigma, c);
  Node asw = d_nodeManager->mkNode(REGEXP_CONCAT, a, sigma, sigmaStar);

  includes(sigma3, abc);
  doesNotInclude(abc, sigma3);

  includes(sigma3, asc);
  doesNotInclude(asc, sigma3);

  includes(asc, abc);
  doesNotInclude(abc, asc);

  includes(asw, asc);
  doesNotInclude(asc, asw);
}

TEST_F(TestTheoryBlackRegexpOperation, star_wildcards)
{
  Node sigma = d_nodeManager->mkNode(REGEXP_SIGMA);
  Node sigmaStar = d_nodeManager->mkNode(REGEXP_STAR, sigma);
  Node a = d_nodeManager->mkNode(STRING_TO_REGEXP,
                                 d_nodeManager->mkConst(String("a")));
  Node c = d_nodeManager->mkNode(STRING_TO_REGEXP,
                                 d_nodeManager->mkConst(String("c")));
  Node abc = d_nodeManager->mkNode(STRING_TO_REGEXP,
                                   d_nodeManager->mkConst(String("abc")));

  Node _abc_ = d_nodeManager->mkNode(REGEXP_CONCAT, sigmaStar, abc, sigmaStar);
  Node _asc_ =
      d_nodeManager->mkNode(REGEXP_CONCAT, {sigmaStar, a, sigma, c, sigmaStar});
  Node _sc_ = Rewriter::rewrite(
      d_nodeManager->mkNode(REGEXP_CONCAT, {sigmaStar, sigma, c, sigmaStar}));
  Node _as_ = Rewriter::rewrite(
      d_nodeManager->mkNode(REGEXP_CONCAT, {sigmaStar, a, sigma, sigmaStar}));
  Node _assc_ = d_nodeManager->mkNode(
      REGEXP_CONCAT,
      std::vector<Node>{sigmaStar, a, sigma, sigma, c, sigmaStar});
  Node _csa_ =
      d_nodeManager->mkNode(REGEXP_CONCAT, {sigmaStar, c, sigma, a, sigmaStar});
  Node _c_a_ = d_nodeManager->mkNode(REGEXP_CONCAT,
                                     {sigmaStar, c, sigmaStar, a, sigmaStar});
  Node _s_s_ = Rewriter::rewrite(d_nodeManager->mkNode(
      REGEXP_CONCAT, {sigmaStar, sigma, sigmaStar, sigma, sigmaStar}));
  Node _a_abc_ = Rewriter::rewrite(d_nodeManager->mkNode(
      REGEXP_CONCAT, {sigmaStar, a, sigmaStar, abc, sigmaStar}));

  includes(_asc_, _abc_);
  doesNotInclude(_abc_, _asc_);
  doesNotInclude(_csa_, _abc_);
  doesNotInclude(_assc_, _asc_);
  doesNotInclude(_asc_, _assc_);
  includes(_sc_, abc);
  includes(_sc_, _abc_);
  includes(_sc_, _asc_);
  includes(_sc_, _assc_);
  doesNotInclude(_sc_, _csa_);
  includes(_as_, abc);
  includes(_as_, _abc_);
  includes(_as_, _asc_);
  includes(_as_, _assc_);
  doesNotInclude(_sc_, _csa_);
  includes(_s_s_, _c_a_);
  doesNotInclude(_c_a_, _s_s_);
  includes(_abc_, _a_abc_);
  doesNotInclude(_a_abc_, _abc_);
}

}  // namespace test
}  // namespace cvc5
