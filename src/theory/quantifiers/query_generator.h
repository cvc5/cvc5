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

/** QueryGenerator
 *
 */
class QueryGenerator
{
 public:
  QueryGenerator();
  ~QueryGenerator() {}
  /** initialize */
  void initialize(SygusSampler* ss, unsigned deqThresh);
  /** add term */
  void addTerm(Node n);

 private:
  /** pointer to the sygus sampler object we are using */
  SygusSampler* d_sampler;
  /** the disequality threshold (number of points)
   * 
   */
  unsigned d_deq_thresh;
  /** the trie, for each type */
  std::map< TypeNode, LazyTrie > d_qgt_trie;
  /** find queries
   * 
   */
  void findQueries(
               LazyTrie * t,
               Node n,
               LazyTrieEvaluator* ev,
               unsigned index,
               unsigned ntotal,
               int deqAllow,
               int eqAllow,
               bool exact
                  );
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__QUANTIFIERS___H */
