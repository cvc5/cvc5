/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/valuation.h"

namespace cvc5::internal {
namespace theory {

class TheoryModel;
class RelevanceManager;

/**
 * Difficulty manager, which tracks an estimate of the difficulty of each
 * preprocessed assertion during solving.
 */
class DifficultyManager : protected EnvObj
{
  typedef context::CDHashSet<Node> NodeSet;
  typedef context::CDHashMap<Node, uint64_t> NodeUIntMap;

 public:
  DifficultyManager(Env& env, RelevanceManager* rlv, Valuation val);
  /** Notify input assertions */
  void notifyInputAssertions(const std::vector<Node>& assertions);
  /**
   * Get difficulty map, which populates dmap mapping preprocessed assertions
   * to a difficulty measure (a constant integer).
   *
   * @param dmap The difficulty map to populate.
   * @param includeLemmas Whether to include difficulty of lemmas in the domain
   * of dmap.
   */
  void getDifficultyMap(std::map<Node, Node>& dmap, bool includeLemmas = false);
  /**
   * Get the current difficulty for input formula or lemma n.
   */
  uint64_t getCurrentDifficulty(const Node& n) const;
  /**
   * Notify lemma, for difficulty measurements based on lemmas, and to
   * subsequently track difficulty for lem. This increments the difficulty
   * of assertions that share literals with that lemma if the difficulty mode
   * is LEMMA_LITERAL. In particular, for each literal lit in the lemma lem, we
   * increment the difficulty of the assertion res[lit], which corresponds to
   * the assertion that was the reason why the literal is relevant in the
   * current context.
   *
   * @param lem The lemma
   * @param inFullEffortCheck Whether we are in a full effort check when the
   * lemma was sent.
   */
  void notifyLemma(Node lem, bool inFullEffortCheck);
  /** Needs candidate model, return true if the method below requires calling */
  bool needsCandidateModel() const;
  /**
   * Notify that `m` is a (candidate) model. This increments the difficulty
   * of assertions that are not satisfied by that model.
   *
   * @param m The candidate model.
   */
  void notifyCandidateModel(TheoryModel* m);

 private:
  /** Increment difficulty on assertion a */
  void incrementDifficulty(TNode a, uint64_t amount = 1);
  /** Pointer to the parent relevance manager */
  RelevanceManager* d_rlv;
  /** The input assertions */
  NodeSet d_input;
  /** The lemmas */
  NodeSet d_lemma;
  /** The valuation object, used to query current value of theory literals */
  Valuation d_val;
  /**
   * User-context dependent mapping from input assertions to difficulty measure
   */
  NodeUIntMap d_dfmap;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__DIFFICULTY_MANAGER__H */
