/*********************                                                        */
/*! \file query_generator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief query_generator
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS___H
#define __CVC4__THEORY__QUANTIFIERS___H

#include <map>
#include "expr/node.h"
#include "theory/quantifiers/lazy_trie.h"
#include "theory/quantifiers/sygus_sampler.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Query generation threshold trie
 *
 *
 */
class QGTTrie
{
 public:
  std::vector<Node> d_nodes;
  std::map<Node, QGTTrie> d_children;
  void addTerm(Node n,
               LazyTrieEvaluator* eval,
               unsigned deqAllow,
               unsigned index,
               unsigned ntotal,
               bool exact = true);
};

/** QueryGenerator
 *
 */
class QueryGenerator
{
 public:
  QueryGenerator();
  ~QueryGenerator() {}
  /** initialize */
  void initialize(SygusSampler* ss);
  /** add term */
  void addTerm(Node n);

 private:
  /** pointer to the sygus sampler object we are using */
  SygusSampler* d_sampler;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__QUANTIFIERS___H */
