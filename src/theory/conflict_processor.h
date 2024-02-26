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
 * Conflict processor module
 */

#include "cvc5_public.h"

#ifndef CVC5__THEORY__CONFLICT_PROCESSOR_H
#define CVC5__THEORY__CONFLICT_PROCESSOR_H

#include "expr/node.h"
#include "expr/subs.h"
#include "proof/trust_node.h"
#include "smt/env_obj.h"
#include "theory/substitutions.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {

class TheoryEngine;
class Assigner;

namespace theory {

/**
 * IDEAS: Use top-level substitutions? combine with inprocess?
 * duplication under substitution?
 * infer substitutions for terms? f(t) where FV(t) not in sigma
 */
class ConflictProcessor : protected EnvObj
{
 public:
  ConflictProcessor(Env& env, TheoryEngine* te);
  ~ConflictProcessor() {}

  TrustNode processLemma(const TrustNode& lem);

 private:
  /** The parent engine */
  TheoryEngine* d_engine;
  Node d_true;
  Node d_false;
  Node d_nullNode;
  /** Use the extended rewriter? */
  bool d_useExtRewriter;
  /** Statistics about the conflict processor */
  struct Statistics
  {
    Statistics(StatisticsRegistry& sr);
    /** Total number of lemmas */
    IntStat d_initLemmas;
    /** Total number of lemmas */
    IntStat d_lemmas;
    /** Total number of minimized lemmas */
    IntStat d_minLemmas;
  };
  Statistics d_stats;
  void decomposeLemma(const Node& lem,
                      SubstitutionMap& s,
                      std::map<Node, Node>& varToExp,
                      std::vector<Node>& tgtLits) const;
  Node evaluateSubstitutionLit(const SubstitutionMap& s,
                               const Node& tgtLit) const;
  Node evaluateSubstitution(const SubstitutionMap& s, const Node& tgtLit) const;
  bool checkSubstitution(const SubstitutionMap& s, const Node& tgtLit) const;
  bool isAssignEq(const SubstitutionMap& s,
                  const Node& n,
                  Node& v,
                  Node& c) const;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__ASSIGNER_H */
