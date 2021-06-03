/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Liana Hadarean, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Algebraic solver.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__BV_SUBTHEORY__INEQUALITY_H
#define CVC5__THEORY__BV__BV_SUBTHEORY__INEQUALITY_H

#include <unordered_set>

#include "context/cdhashset.h"
#include "expr/attribute.h"
#include "theory/bv/bv_inequality_graph.h"
#include "theory/bv/bv_subtheory.h"

namespace cvc5 {
namespace theory {
namespace bv {

/** Cache for InequalitySolver::isInequalityOnly() */
struct IneqOnlyAttributeId
{
};
typedef expr::Attribute<IneqOnlyAttributeId, bool> IneqOnlyAttribute;

/** Whether the above has been computed yet or not for an expr */
struct IneqOnlyComputedAttributeId
{
};
typedef expr::Attribute<IneqOnlyComputedAttributeId, bool>
    IneqOnlyComputedAttribute;

class InequalitySolver : public SubtheorySolver
{
  struct Statistics
  {
    IntStat d_numCallstoCheck;
    TimerStat d_solveTime;
    Statistics();
  };

  context::CDHashSet<Node> d_assertionSet;
  InequalityGraph d_inequalityGraph;
  context::CDHashMap<Node, TNode> d_explanations;
  context::CDO<bool> d_isComplete;
  typedef std::unordered_set<Node> NodeSet;
  NodeSet d_ineqTerms;
  bool isInequalityOnly(TNode node);
  bool addInequality(TNode a, TNode b, bool strict, TNode fact);
  Statistics d_statistics;

 public:
  InequalitySolver(context::Context* c, context::Context* u, BVSolverLazy* bv)
      : SubtheorySolver(c, bv),
        d_assertionSet(c),
        d_inequalityGraph(c, u),
        d_explanations(c),
        d_isComplete(c, true),
        d_ineqTerms(),
        d_statistics()
  {
  }

  bool check(Theory::Effort e) override;
  void propagate(Theory::Effort e) override;
  void explain(TNode literal, std::vector<TNode>& assumptions) override;
  bool isComplete() override { return d_isComplete; }
  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;
  Node getModelValue(TNode var) override;
  EqualityStatus getEqualityStatus(TNode a, TNode b) override;
  void assertFact(TNode fact) override;
  void preRegister(TNode node) override;
};

}  // namespace bv
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__BV__BV_SUBTHEORY__INEQUALITY_H */
