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

#include "expr/node.h"
#include "expr/node_manager.h"
#include "theory/strings/skolem_cache.h"
#include "util/rational.h"
#include "util/string.h"

using namespace CVC4;
using namespace CVC4::theory::strings;

class TheoryStringsSkolemCacheBlack : public CxxTest::TestSuite
{
 public:
  void setUp() override
  {
    d_nm.reset(new NodeManager(nullptr));
    d_scope.reset(new NodeManagerScope(d_nm.get()));
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

    // Check that skolems are shared between:
    //
    // SK_FIRST_CTN(c, b)
    //
    // SK_FIRST_CTN((str.substr c), b)
    {
      Node s1 = sk.mkSkolemCached(c, b, SkolemCache::SK_FIRST_CTN_PRE, "foo");
      Node s2 = sk.mkSkolemCached(sc, b, SkolemCache::SK_FIRST_CTN_PRE, "foo");
      TS_ASSERT_EQUALS(s1, s2);
    }

    // Check that skolems are shared between:
    //
    // SK_PURIFY((str.substr a 0 (str.indexof a b 0)))
    //
    // SK_FIRST_CTN(a, b)
    {
      Node s1 = sk.mkSkolemCached(sa, b, SkolemCache::SK_PURIFY, "foo");
      Node s2 = sk.mkSkolemCached(a, b, SkolemCache::SK_FIRST_CTN_PRE, "foo");
      TS_ASSERT_EQUALS(s1, s2);
    }
  }

 private:
  std::unique_ptr<NodeManager> d_nm;
  std::unique_ptr<NodeManagerScope> d_scope;
};
