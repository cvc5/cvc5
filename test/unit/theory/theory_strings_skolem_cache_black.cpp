/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andres Noetzli, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the skolem cache of the theory of strings.
 */

#include <memory>

#include "expr/node.h"
#include "test_smt.h"
#include "theory/strings/skolem_cache.h"
#include "util/rational.h"
#include "util/string.h"

namespace cvc5 {

using namespace theory::strings;

namespace test {

class TestTheoryBlackStringsSkolemCache : public TestSmt
{
};

TEST_F(TestTheoryBlackStringsSkolemCache, mkSkolemCached)
{
  Node zero = d_nodeManager->mkConst(Rational(0));
  Node n = d_skolemManager->mkDummySkolem("n", d_nodeManager->integerType());
  Node a = d_skolemManager->mkDummySkolem("a", d_nodeManager->stringType());
  Node b = d_skolemManager->mkDummySkolem("b", d_nodeManager->stringType());
  Node c = d_skolemManager->mkDummySkolem("c", d_nodeManager->stringType());
  Node d = d_skolemManager->mkDummySkolem("d", d_nodeManager->stringType());
  Node sa = d_nodeManager->mkNode(
      kind::STRING_SUBSTR,
      a,
      zero,
      d_nodeManager->mkNode(kind::STRING_STRIDOF, a, b, zero));
  Node sc = d_nodeManager->mkNode(kind::STRING_SUBSTR, c, zero, n);

  SkolemCache sk;

  // Check that skolems are shared between:
  //
  // SK_FIRST_CTN(a, b)
  //
  // SK_FIRST_CTN(a, b)
  {
    Node s1 = sk.mkSkolemCached(a, b, SkolemCache::SK_FIRST_CTN_PRE, "foo");
    Node s2 = sk.mkSkolemCached(a, b, SkolemCache::SK_FIRST_CTN_PRE, "foo");
    ASSERT_EQ(s1, s2);
  }
}
}  // namespace test
}  // namespace cvc5
