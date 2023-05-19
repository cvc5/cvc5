/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * multi inst match generator class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__INST_MATCH_GENERATOR_MULTI_H
#define CVC5__THEORY__QUANTIFIERS__INST_MATCH_GENERATOR_MULTI_H

#include <map>
#include <vector>
#include "expr/node_trie.h"
#include "theory/quantifiers/ematching/inst_match_generator.h"
#include "theory/quantifiers/inst_match_trie.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace inst {

/** InstMatchGeneratorMulti
 *
 * This is an earlier implementation of multi-triggers that is enabled by
 * --multi-trigger-cache. This generator takes the product of instantiations
 * found by single trigger matching, and does not have the guarantee that the
 * number of instantiations is polynomial wrt the number of ground terms.
 */
class InstMatchGeneratorMulti : public IMGenerator
{
 public:
  /** constructors */
  InstMatchGeneratorMulti(Env& env,
                          Trigger* tparent,
                          Node q,
                          std::vector<Node>& pats);
  /** destructor */
  ~InstMatchGeneratorMulti() override;

  /** Reset instantiation round. */
  void resetInstantiationRound() override;
  /** Reset. */
  bool reset(Node eqc) override;
  /** Add instantiations. */
  uint64_t addInstantiations(InstMatch& m) override;

 private:
  /** process new match
   *
   * Called during addInstantiations(...).
   * Indicates we produced a match m for child fromChildIndex
   * addedLemmas is how many instantiations we succesfully send
   * via IMGenerator::sendInstantiation(...) calls.
   */
  void processNewMatch(InstMatch& m,
                       size_t fromChildIndex,
                       uint64_t& addedLemmas);
  /** helper for process new match
   * tr is the inst match trie (term index) we are currently traversing.
   * trieIndex is depth we are in trie tr.
   * childIndex is the index of the term in the multi trigger we are currently
   *               processing.
   * endChildIndex is the index of the term in the multi trigger that generated
   *                  a new term, and hence we will end when the product
   *                  computed by this function returns to.
   * modEq is whether we are matching modulo equality.
   */
  void processNewInstantiations(InstMatch& m,
                                uint64_t& addedLemmas,
                                InstMatchTrie* tr,
                                size_t trieIndex,
                                size_t childIndex,
                                size_t endChildIndex,
                                bool modEq);
  /** Map from pattern nodes to indices of variables they contain. */
  std::map<Node, std::vector<uint64_t> > d_var_contains;
  /** Map from variable indices to pattern nodes that contain them. */
  std::map<uint64_t, std::vector<Node> > d_var_to_node;
  /** quantified formula we are producing matches for */
  Node d_quant;
  /** children generators
   * These are inst match generators for each term in the multi trigger.
   */
  std::vector<InstMatchGenerator*> d_children;
  /** variable orderings
   * Stores a heuristically determined variable ordering (unique
   * variables first) for each term in the multi trigger.
   */
  std::map<size_t, InstMatchTrie::ImtIndexOrder*> d_imtio;
  /** inst match tries for each child node
   * This data structure stores all InstMatch objects generated
   * by matching for each term in the multi trigger.
   */
  std::vector<InstMatchTrieOrdered> d_children_trie;
};

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
