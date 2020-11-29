/*********************                                                        */
/*! \file regexp_operation_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Unit tests for symbolic regular expression operations
 **
 ** Unit tests for symbolic regular expression operations.
 **/

#include <cxxtest/TestSuite.h>

#include <iostream>
#include <memory>
#include <vector>

#include "api/cvc4cpp.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/rewriter.h"
#include "theory/strings/regexp_operation.h"
#include "theory/strings/skolem_cache.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::smt;
using namespace CVC4::theory;
using namespace CVC4::theory::strings;

class RegexpOperationBlack : public CxxTest::TestSuite
{
 public:
  RegexpOperationBlack() {}

  void setUp() override
  {
    Options opts;
    opts.setOutputLanguage(language::output::LANG_SMTLIB_V2);
    d_slv = new api::Solver();
    d_em = d_slv->getExprManager();
    d_smt = d_slv->getSmtEngine();
    d_scope = new SmtScope(d_smt);
    d_skc = new SkolemCache();
    d_regExpOpr = new RegExpOpr(d_skc);

    // Ensure that the SMT engine is fully initialized (required for the
    // rewriter)
    d_smt->push();

    d_nm = NodeManager::currentNM();
  }

  void tearDown() override
  {
    delete d_regExpOpr;
    delete d_skc;
    delete d_scope;
    delete d_slv;
  }

  void includes(Node r1, Node r2)
  {
    r1 = Rewriter::rewrite(r1);
    r2 = Rewriter::rewrite(r2);
    std::cout << r1 << " includes " << r2 << std::endl;
    TS_ASSERT(d_regExpOpr->regExpIncludes(r1, r2));
  }

  void doesNotInclude(Node r1, Node r2)
  {
    r1 = Rewriter::rewrite(r1);
    r2 = Rewriter::rewrite(r2);
    std::cout << r1 << " does not include " << r2 << std::endl;
    TS_ASSERT(!d_regExpOpr->regExpIncludes(r1, r2));
  }

  void testBasic()
  {
    Node sigma = d_nm->mkNode(REGEXP_SIGMA, std::vector<Node>{});
    Node sigmaStar = d_nm->mkNode(REGEXP_STAR, sigma);
    Node a = d_nm->mkNode(STRING_TO_REGEXP, d_nm->mkConst(String("a")));
    Node c = d_nm->mkNode(STRING_TO_REGEXP, d_nm->mkConst(String("c")));
    Node abc = d_nm->mkNode(STRING_TO_REGEXP, d_nm->mkConst(String("abc")));
    Node sigma3 = d_nm->mkNode(REGEXP_CONCAT, sigma, sigma, sigma);
    Node asc = d_nm->mkNode(REGEXP_CONCAT, a, sigma, c);
    Node asw = d_nm->mkNode(REGEXP_CONCAT, a, sigma, sigmaStar);

    includes(sigma3, abc);
    doesNotInclude(abc, sigma3);

    includes(sigma3, asc);
    doesNotInclude(asc, sigma3);

    includes(asc, abc);
    doesNotInclude(abc, asc);

    includes(asw, asc);
    doesNotInclude(asc, asw);
  }

  void testStarWildcards()
  {
    Node sigma = d_nm->mkNode(REGEXP_SIGMA, std::vector<Node>{});
    Node sigmaStar = d_nm->mkNode(REGEXP_STAR, sigma);
    Node a = d_nm->mkNode(STRING_TO_REGEXP, d_nm->mkConst(String("a")));
    Node c = d_nm->mkNode(STRING_TO_REGEXP, d_nm->mkConst(String("c")));
    Node abc = d_nm->mkNode(STRING_TO_REGEXP, d_nm->mkConst(String("abc")));

    Node _abc_ = d_nm->mkNode(REGEXP_CONCAT, sigmaStar, abc, sigmaStar);
    Node _asc_ = d_nm->mkNode(REGEXP_CONCAT, sigmaStar, a, sigma, c, sigmaStar);
    Node _sc_ = Rewriter::rewrite(
        d_nm->mkNode(REGEXP_CONCAT, sigmaStar, sigma, c, sigmaStar));
    Node _as_ = Rewriter::rewrite(
        d_nm->mkNode(REGEXP_CONCAT, sigmaStar, a, sigma, sigmaStar));
    Node _assc_ = d_nm->mkNode(
        REGEXP_CONCAT,
        std::vector<Node>{sigmaStar, a, sigma, sigma, c, sigmaStar});
    Node _csa_ = d_nm->mkNode(REGEXP_CONCAT, sigmaStar, c, sigma, a, sigmaStar);
    Node _c_a_ =
        d_nm->mkNode(REGEXP_CONCAT, sigmaStar, c, sigmaStar, a, sigmaStar);
    Node _s_s_ = Rewriter::rewrite(d_nm->mkNode(
        REGEXP_CONCAT, sigmaStar, sigma, sigmaStar, sigma, sigmaStar));
    Node _a_abc_ = Rewriter::rewrite(
        d_nm->mkNode(REGEXP_CONCAT, sigmaStar, a, sigmaStar, abc, sigmaStar));

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

 private:
  api::Solver* d_slv;
  ExprManager* d_em;
  SmtEngine* d_smt;
  SmtScope* d_scope;
  SkolemCache* d_skc;
  RegExpOpr* d_regExpOpr;

  NodeManager* d_nm;
};
