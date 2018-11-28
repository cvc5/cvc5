/*********************                                                        */
/*! \file node_trie_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of (T)NodeTrie.
 **/

#include <cxxtest/TestSuite.h>

#include <memory>

#include "expr/node.h"
#include "expr/node_manager.h"
#include "expr/node_trie.h"
#include "util/rational.h"

using namespace CVC4;

class NodeTrieBlack : public CxxTest::TestSuite
{
 public:
  void setUp() override
  {
    d_nm.reset(new NodeManager(nullptr));
    d_scope.reset(new NodeManagerScope(d_nm.get()));
  }

  void tearDown() override {}

  void testExistsPrefix()
  {
    theory::NodeTrie nt;
    Node zero = d_nm->mkConst(Rational(0));
    Node one = d_nm->mkConst(Rational(1));
    Node two = d_nm->mkConst(Rational(2));
    Node three = d_nm->mkConst(Rational(3));

    nt.addTerm(zero, {one, one, three});
    nt.addTerm(one, {one, three});
    nt.addTerm(two, {one, two, three, one});

    // Single element with index prefix in trie
    TS_ASSERT_EQUALS(nt.existsPrefix({one, two}), two);
    // Index prefix is actually the whole prefix
    TS_ASSERT_EQUALS(nt.existsPrefix({one, three}), one);
    // Index prefix not in trie
    TS_ASSERT_EQUALS(nt.existsPrefix({two, three}), Node::null());
    // Index prefix not in trie and index prefix corresponds to existing index
    // ([1, 3]) + element (1)
    TS_ASSERT_EQUALS(nt.existsPrefix({one, three, one}), Node::null());
  }

 private:
  std::unique_ptr<NodeManager> d_nm;
  std::unique_ptr<NodeManagerScope> d_scope;
};
