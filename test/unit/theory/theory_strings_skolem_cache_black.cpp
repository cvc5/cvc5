/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

using namespace cvc5::internal::kind;
using namespace cvc5::internal::theory::strings;

namespace cvc5::internal {
namespace test {

class TestTheoryBlackStringsSkolemCache : public TestSmt
{
};

TEST_F(TestTheoryBlackStringsSkolemCache, mkSkolemCached)
{
  Node zero = d_nodeManager->mkConstInt(Rational(0));
  Node n = d_skolemManager->mkDummySkolem("n", d_nodeManager->integerType());
  Node a = d_skolemManager->mkDummySkolem("a", d_nodeManager->stringType());
  Node b = d_skolemManager->mkDummySkolem("b", d_nodeManager->stringType());
  Node c = d_skolemManager->mkDummySkolem("c", d_nodeManager->stringType());
  Node d = d_skolemManager->mkDummySkolem("d", d_nodeManager->stringType());
  Node sa = d_nodeManager->mkNode(
      kind::STRING_SUBSTR,
      a,
      zero,
      d_nodeManager->mkNode(kind::STRING_INDEXOF, a, b, zero));
  Node sc = d_nodeManager->mkNode(kind::STRING_SUBSTR, c, zero, n);

  SkolemCache sk(nullptr);

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
}  // namespace cvc5::internal
