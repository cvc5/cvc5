/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Algorithms for node tries
 */

#include "cvc5_private.h"

#ifndef CVC5__EXPR__NODE_TRIE_ALGORITHM_H
#define CVC5__EXPR__NODE_TRIE_ALGORITHM_H

#include <map>
#include "expr/node_trie.h"

namespace cvc5 {

/** 
 * A virtual base class for the algorithm below.
 */
class NodeTriePathCompareCallback
{
public:
  NodeTriePathCompareCallback() {}
  virtual ~NodeTriePathCompareCallback(){}
  /** Whether to consider a fork in the path in a trie */
  virtual bool considerFork(TNode a, TNode b) = 0;
  /** Process leaves */
  virtual void processData(TNode fa, TNode fb) = 0;
};


/**
 * Given a TNode trie of arity n, this calls ntpc.processData(fa, fb) on all
 * pairs of distinct leaves fa and fb in t at paths [fa1, ..., fan]
 * [fb1, ..., fbn] such that ntpc.considerFork(fai, fbi) returns true for all
 * i = 1, ..., n.
 */
void nodeTriePathCompare(const TNodeTrie* t, size_t n, NodeTriePathCompareCallback& ntpc);

}  // namespace cvc5

#endif /* CVC5__EXPR__NODE_TRIE_ALGORITHM_H */
