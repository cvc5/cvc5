/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Unit tests for the strings word utilities
 */

#include <iostream>
#include <memory>
#include <vector>

#include "expr/node.h"
#include "test_node.h"
#include "theory/strings/word.h"
#include "util/string.h"

namespace cvc5::internal {

using namespace theory;
using namespace theory::strings;

namespace test {

class TestTheoryWhiteStringsWord : public TestNode
{
};

TEST_F(TestTheoryWhiteStringsWord, strings)
{
  Node empty = d_nodeManager->mkConst(String(""));
  Node a = d_nodeManager->mkConst(String("a"));
  Node b = d_nodeManager->mkConst(String("b"));
  Node aa = d_nodeManager->mkConst(String("aa"));
  Node aaaaa = d_nodeManager->mkConst(String("aaaaa"));
  Node abc = d_nodeManager->mkConst(String("abc"));
  Node bbc = d_nodeManager->mkConst(String("bbc"));
  Node cac = d_nodeManager->mkConst(String("cac"));
  Node abca = d_nodeManager->mkConst(String("abca"));

  TypeNode stringType = d_nodeManager->stringType();
  ASSERT_TRUE(Word::mkEmptyWord(stringType) == empty);

  std::vector<Node> vec;
  vec.push_back(abc);
  Node abcMk = Word::mkWordFlatten(vec);
  ASSERT_EQ(abc, abcMk);
  vec.push_back(a);
  Node abcaMk = Word::mkWordFlatten(vec);
  ASSERT_EQ(abca, abcaMk);

  ASSERT_TRUE(Word::getLength(empty) == 0);
  ASSERT_TRUE(Word::getLength(aaaaa) == 5);

  ASSERT_TRUE(Word::isEmpty(empty));
  ASSERT_FALSE(Word::isEmpty(a));

  ASSERT_TRUE(Word::find(empty, empty) == 0);
  ASSERT_TRUE(Word::find(a, empty) == 0);
  ASSERT_TRUE(Word::find(empty, empty, 1) == std::string::npos);
  ASSERT_TRUE(Word::find(cac, a, 0) == 1);
  ASSERT_TRUE(Word::find(cac, abc) == std::string::npos);

  ASSERT_TRUE(Word::rfind(aaaaa, empty) == 0);
  ASSERT_TRUE(Word::rfind(aaaaa, a) == 0);
  ASSERT_TRUE(Word::rfind(abca, abc, 1) == 1);

  ASSERT_TRUE(Word::hasPrefix(empty, empty));
  ASSERT_TRUE(Word::hasPrefix(a, empty));
  ASSERT_TRUE(Word::hasPrefix(aaaaa, a));
  ASSERT_FALSE(Word::hasPrefix(abca, b));
  ASSERT_FALSE(Word::hasPrefix(empty, a));

  ASSERT_TRUE(Word::hasSuffix(empty, empty));
  ASSERT_TRUE(Word::hasSuffix(a, empty));
  ASSERT_TRUE(Word::hasSuffix(a, a));
  ASSERT_FALSE(Word::hasSuffix(abca, b));
  ASSERT_FALSE(Word::hasSuffix(empty, abc));

  ASSERT_EQ(bbc, Word::replace(abc, a, b));
  ASSERT_EQ(aaaaa, Word::replace(aaaaa, b, a));
  ASSERT_EQ(aa, Word::replace(a, empty, a));

  ASSERT_EQ(empty, Word::substr(a, 1));
  ASSERT_EQ(empty, Word::substr(empty, 0));
  ASSERT_EQ(a, Word::substr(abca, 3));

  ASSERT_EQ(a, Word::substr(abc, 0, 1));
  ASSERT_EQ(aa, Word::substr(aaaaa, 3, 2));

  ASSERT_EQ(a, Word::prefix(a, 1));
  ASSERT_EQ(empty, Word::prefix(empty, 0));
  ASSERT_EQ(a, Word::prefix(aaaaa, 1));

  ASSERT_EQ(a, Word::suffix(a, 1));
  ASSERT_EQ(empty, Word::suffix(empty, 0));
  ASSERT_EQ(aa, Word::suffix(aaaaa, 2));

  ASSERT_FALSE(Word::noOverlapWith(abc, empty));
  ASSERT_TRUE(Word::noOverlapWith(cac, aa));
  ASSERT_FALSE(Word::noOverlapWith(cac, abc));
  ASSERT_TRUE(Word::noOverlapWith(cac, b));
  ASSERT_FALSE(Word::noOverlapWith(cac, a));
  ASSERT_FALSE(Word::noOverlapWith(abca, a));

  ASSERT_TRUE(Word::overlap(abc, empty) == 0);
  ASSERT_TRUE(Word::overlap(aaaaa, abc) == 1);
  ASSERT_TRUE(Word::overlap(cac, abc) == 0);
  ASSERT_TRUE(Word::overlap(empty, abc) == 0);
  ASSERT_TRUE(Word::overlap(aaaaa, aa) == 2);

  ASSERT_TRUE(Word::roverlap(abc, empty) == 0);
  ASSERT_TRUE(Word::roverlap(aaaaa, abc) == 0);
  ASSERT_TRUE(Word::roverlap(cac, abc) == 1);
  ASSERT_TRUE(Word::roverlap(empty, abc) == 0);
  ASSERT_TRUE(Word::roverlap(aaaaa, aa) == 2);
}
}  // namespace test
}  // namespace cvc5::internal
