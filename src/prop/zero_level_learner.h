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
 * Learner for literals asserted at level zero.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__ZERO_LEVEL_LEARNER_H
#define CVC5__PROP__ZERO_LEVEL_LEARNER_H

#include <unordered_set>

#include "context/cdhashset.h"
#include "context/cdo.h"
#include "expr/node.h"
#include "expr/subs.h"
#include "prop/learned_db.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

class TheoryEngine;

namespace prop {

/**
 * The module for processing literals that are learned at decision level zero.
 *
 * This tracks the literals that are asserted at decision level zero. It
 * computes which literals are "learnable", which currently is limited to those
 * that are over atoms that appear in the input assertions.
 *
 * The module can be queried for the set of learned literals, and also is
 * responsible for printing the literals it learns.
 */
class ZeroLevelLearner : protected EnvObj
{
  using NodeSet = context::CDHashSet<Node>;

 public:
  ZeroLevelLearner(Env& env, TheoryEngine* theoryEngine);

  ~ZeroLevelLearner();

  void notifyTopLevelSubstitution(const Node& lhs, const Node& rhs);
  /** Notify the input formulas and the skolem map */
  void notifyInputFormulas(const std::vector<Node>& assertions);
  /**
   * Notify the given literal was asserted at the given assertion level.
   * Return false if a deep restart is requested.
   */
  bool notifyAsserted(TNode assertion, int32_t alevel);

  /** Get the zero-level assertions */
  std::vector<Node> getLearnedZeroLevelLiterals(
      modes::LearnedLitType ltype) const;
  /** Get the zero-level assertions that should be used on deep restart */
  std::vector<Node> getLearnedZeroLevelLiteralsForRestart() const;
  /** compute type for learned literal */
  modes::LearnedLitType computeLearnedLiteralType(const Node& lit);

 private:
  static void getAtoms(TNode a,
                       std::unordered_set<TNode>& visited,
                       std::unordered_set<Node>& atoms);
  /** Process learned literal */
  void processLearnedLiteral(const Node& lit, modes::LearnedLitType ltype);
  /** is learnable based on the value of options */
  bool isLearnable(modes::LearnedLitType ltype) const;
  /** get solved */
  bool getSolved(const Node& lit, Subs& subs);
  /** has learned literal */
  bool hasLearnedLiteralForRestart() const;

  /** The theory engine we are using */
  TheoryEngine* d_theoryEngine;

  /** Set of literals that hold at level 0 */
  NodeSet d_levelZeroAsserts;

  /** What we have learned */
  LearnedDb d_ldb;

  /** Whether we have seen an assertion level > 0 */
  context::CDO<bool> d_nonZeroAssert;

  /**
   * Atoms of literals from the input formula that were not learned at
   * preprocess.
   */
  NodeSet d_ppnAtoms;
  /** Subterms of the above atoms. */
  NodeSet d_ppnTerms;
  /** Symbols in the above atoms. */
  NodeSet d_ppnSyms;
  /** Current counter of assertions */
  size_t d_assertNoLearnCount;
  /** The threshold */
  size_t d_deepRestartThreshold;
  /** learnable learned literal types (for deep restart), based on option */
  std::unordered_set<modes::LearnedLitType> d_learnedTypes;
}; /* class ZeroLevelLearner */

}  // namespace prop
}  // namespace cvc5::internal

#endif
