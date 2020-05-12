/*********************                                                        */
/*! \file theory_strings_skolem_cache_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of the skolem cache of the theory of strings.
 **/

#include <cxxtest/TestSuite.h>

#include <memory>

#include "expr/expr_manager.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/strings/skolem_cache.h"
#include "util/rational.h"
#include "util/string.h"

using namespace CVC4;
using namespace CVC4::smt;
using namespace CVC4::theory::strings;

class TheoryStringsSkolemCacheBlack : public CxxTest::TestSuite
{
 public:
  void setUp() override
  {
    d_em.reset(new ExprManager());
    d_smt.reset(new SmtEngine(d_em.get()));
    d_scope.reset(new SmtScope(d_smt.get()));
    // Ensure that the SMT engine is fully initialized (required for the
    // rewriter)
    d_smt->push();

    d_nm = NodeManager::fromExprManager(d_em.get());
  }

  void tearDown() override {}

  void testMkSkolemCached()
  {
    Node zero = d_nm->mkConst(Rational(0));
    Node n = d_nm->mkSkolem("n", d_nm->integerType());
    Node a = d_nm->mkSkolem("a", d_nm->stringType());
    Node b = d_nm->mkSkolem("b", d_nm->stringType());
    Node c = d_nm->mkSkolem("c", d_nm->stringType());
    Node d = d_nm->mkSkolem("d", d_nm->stringType());
    Node sa = d_nm->mkNode(kind::STRING_SUBSTR,
                           a,
                           zero,
                           d_nm->mkNode(kind::STRING_STRIDOF, a, b, zero));
    Node sc = d_nm->mkNode(kind::STRING_SUBSTR, c, zero, n);

    SkolemCache sk;

    // Check that skolems are shared between:
    //
    // SK_FIRST_CTN(a, b)
    //
    // SK_FIRST_CTN(a, b)
    {
      Node s1 = sk.mkSkolemCached(a, b, SkolemCache::SK_FIRST_CTN_PRE, "foo");
      Node s2 = sk.mkSkolemCached(a, b, SkolemCache::SK_FIRST_CTN_PRE, "foo");
      TS_ASSERT_EQUALS(s1, s2);
    }
  }

 private:
  std::unique_ptr<ExprManager> d_em;
  std::unique_ptr<SmtEngine> d_smt;
  NodeManager* d_nm;
  std::unique_ptr<SmtScope> d_scope;
};
