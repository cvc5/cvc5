/*********************                                                        */
/*! \file theory_bags.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bags theory.
 **/

#include "theory/bags/theory_bags.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace bags {

TheoryBags::TheoryBags(context::Context* c,
                       context::UserContext* u,
                       OutputChannel& out,
                       Valuation valuation,
                       const LogicInfo& logicInfo,
                       ProofNodeManager* pnm)
    : Theory(THEORY_BAGS, c, u, out, valuation, logicInfo, pnm),
      d_state(c, u, valuation),
      d_im(*this, d_state, pnm),
      d_notify(*this, d_im),
      d_statistics(),
      d_rewriter(&d_statistics.d_rewrites)
{
  // use the official theory state and inference manager objects
  d_theoryState = &d_state;
  d_inferManager = &d_im;
}

TheoryBags::~TheoryBags() {}

TheoryRewriter* TheoryBags::getTheoryRewriter() { return &d_rewriter; }

bool TheoryBags::needsEqualityEngine(EeSetupInfo& esi)
{
  esi.d_notify = &d_notify;
  esi.d_name = "theory::bags::ee";
  return true;
}

void TheoryBags::finishInit()
{
  Assert(d_equalityEngine != nullptr);

  // choice is used to eliminate witness
  d_valuation.setUnevaluatedKind(WITNESS);

  // functions we are doing congruence over
  d_equalityEngine->addFunctionKind(UNION_MAX);
  d_equalityEngine->addFunctionKind(UNION_DISJOINT);
  d_equalityEngine->addFunctionKind(INTERSECTION_MIN);
  d_equalityEngine->addFunctionKind(DIFFERENCE_SUBTRACT);
  d_equalityEngine->addFunctionKind(DIFFERENCE_REMOVE);
  d_equalityEngine->addFunctionKind(BAG_COUNT);
  d_equalityEngine->addFunctionKind(MK_BAG);
  d_equalityEngine->addFunctionKind(BAG_CARD);
}

void TheoryBags::postCheck(Effort level) {}

void TheoryBags::notifyFact(TNode atom,
                            bool polarity,
                            TNode fact,
                            bool isInternal)
{
}

bool TheoryBags::collectModelValues(TheoryModel* m,
                                    const std::set<Node>& termBag)
{
  return true;
}

TrustNode TheoryBags::explain(TNode node) { return d_im.explainLit(node); }

Node TheoryBags::getModelValue(TNode node) { return Node::null(); }

void TheoryBags::preRegisterTerm(TNode node) {}

TrustNode TheoryBags::expandDefinition(Node n)
{
  // TODO(projects#224): add choose and is_singleton here
  return TrustNode::null();
}

void TheoryBags::presolve() {}

/**************************** eq::NotifyClass *****************************/

void TheoryBags::eqNotifyNewClass(TNode t)
{
  Assert(false) << "Not implemented yet" << std::endl;
}

void TheoryBags::eqNotifyMerge(TNode t1, TNode t2)
{
  Assert(false) << "Not implemented yet" << std::endl;
}

void TheoryBags::eqNotifyDisequal(TNode t1, TNode t2, TNode reason)
{
  Assert(false) << "Not implemented yet" << std::endl;
}

void TheoryBags::NotifyClass::eqNotifyNewClass(TNode t)
{
  Debug("bags-eq") << "[bags-eq] eqNotifyNewClass:"
                   << " t = " << t << std::endl;
  d_theory.eqNotifyNewClass(t);
}

void TheoryBags::NotifyClass::eqNotifyMerge(TNode t1, TNode t2)
{
  Debug("bags-eq") << "[bags-eq] eqNotifyMerge:"
                   << " t1 = " << t1 << " t2 = " << t2 << std::endl;
  d_theory.eqNotifyMerge(t1, t2);
}

void TheoryBags::NotifyClass::eqNotifyDisequal(TNode t1, TNode t2, TNode reason)
{
  Debug("bags-eq") << "[bags-eq] eqNotifyDisequal:"
                   << " t1 = " << t1 << " t2 = " << t2 << " reason = " << reason
                   << std::endl;
  d_theory.eqNotifyDisequal(t1, t2, reason);
}

}  // namespace bags
}  // namespace theory
}  // namespace CVC4
