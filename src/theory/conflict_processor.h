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
#include "util/statistics_stats.h"

namespace cvc5::internal {

class TheoryEngine;
class Assigner;

namespace theory {

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
  Node d_nullNode;
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
                      Subs& s,
                      std::map<Node, Node>& varToExp,
                      std::vector<TNode>& tgtLits) const;
  Node evaluateSubstitution(const Subs& s, const Node& tgtLit) const;
  bool checkSubstitution(const Subs& s, const Node& tgtLit, bool expect) const;
  /**
   * Get entailed equalities from literal cube tc.
   */
  static void getEntailedEq(const Node& tc,
                            const std::map<Node, size_t>& vindex,
                            std::vector<Node>& entval);
  static bool isAssignEq(const Node& n, Node& v, Node& c, bool reqConst = true);
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__ASSIGNER_H */
