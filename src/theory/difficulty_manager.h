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
 * Relevance manager.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__DIFFICULTY_MANAGER__H
#define CVC5__THEORY__DIFFICULTY_MANAGER__H

#include <unordered_map>
#include <unordered_set>

#include "context/cdhashmap.h"
#include "context/cdlist.h"
#include "expr/node.h"
#include "theory/valuation.h"

namespace cvc5 {

class Env;

namespace theory {

class TheoryModel;

/**
 */
class DifficultyManager
{
  typedef context::CDList<Node> NodeList;
  typedef context::CDHashMap<Node, uint64_t> NodeUIntMap;

 public:
  DifficultyManager(Env& env, Valuation val);
  /**
   * Get difficulty map
   */
  void getDifficultyMap(std::map<Node, Node>& dmap);
  /** Notify lemma, for difficulty measurements */
  void notifyLemma(const std::map<TNode, TNode>& rse, Node n);
  /** Notify that tm is a (candidate) model */
  void notifyCandidateModel(const NodeList& input, TheoryModel* m);

 private:
  /** Increment difficulty on assertion a */
  void incrementDifficulty(TNode a, uint64_t amount=1);
  /** The valuation object, used to query current value of theory literals */
  Valuation d_val;
  /** 
   * user-context dependent mapping from input assertions to difficulty measure
   */
  NodeUIntMap d_dfmap;
};

}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__DIFFICULTY_MANAGER__H */
