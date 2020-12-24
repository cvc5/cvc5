/*********************                                                        */
/*! \file theory_bags.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bags theory.
 **/

#include "theory/bags/theory_bags.h"

#include "theory/bags/inference_generator.h"

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
      d_im(*this, d_state, nullptr),
      d_notify(*this, d_im),
      d_statistics(),
      d_rewriter(&d_statistics.d_rewrites),
      d_termReg(d_state, d_im),
      d_solver(d_state, d_im, d_termReg)
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
  d_equalityEngine->addFunctionKind(DUPLICATE_REMOVAL);
  d_equalityEngine->addFunctionKind(MK_BAG);
  d_equalityEngine->addFunctionKind(BAG_CARD);
  d_equalityEngine->addFunctionKind(BAG_FROM_SET);
  d_equalityEngine->addFunctionKind(BAG_TO_SET);
}

void TheoryBags::postCheck(Effort effort)
{
  d_im.doPendingFacts();
  // TODO: clean this before merge Assert(d_strat.isStrategyInit());
  if (!d_state.isInConflict() && !d_valuation.needCheck())
  // TODO: clean this before merge && d_strat.hasStrategyEffort(e))
  {
    Trace("bags::TheoryBags::postCheck") << "effort: " << std::endl;

    // TODO: clean this before merge ++(d_statistics.d_checkRuns);
    bool sentLemma = false;
    bool hadPending = false;
    Trace("bags-check") << "Full effort check..." << std::endl;
    do
    {
      d_im.reset();
      // TODO: clean this before merge ++(d_statistics.d_strategyRuns);
      Trace("bags-check") << "  * Run strategy..." << std::endl;
      // TODO: clean this before merge runStrategy(e);

      for (std::pair<const TypeNode, std::vector<Node>>& t : d_state.getBags())
      {
        for (Node& n : t.second)
        {
          std::cout << n << std::endl;
          Kind k = n.getKind();
          switch (k)
          {
            case kind::DIFFERENCE_SUBTRACT:
              for (Node& e : d_state.getElements(t.first.getBagElementType()))
              {
                InferenceGenerator ig(NodeManager::currentNM());
                InferInfo i = ig.differenceSubtract(n, e);
                i.d_im = &d_im;
                i.process(&d_im, true);
              }
            default: break;
          }
        }
      }

      d_solver.checkNormalFormsEq();
      d_solver.checkNormalFormsDeq();
      // remember if we had pending facts or lemmas
      hadPending = d_im.hasPending();
      // Send the facts *and* the lemmas. We send lemmas regardless of whether
      // we send facts since some lemmas cannot be dropped. Other lemmas are
      // otherwise avoided by aborting the strategy when a fact is ready.
      d_im.doPending();
      // Did we successfully send a lemma? Notice that if hasPending = true
      // and sentLemma = false, then the above call may have:
      // (1) had no pending lemmas, but successfully processed pending facts,
      // (2) unsuccessfully processed pending lemmas.
      // In either case, we repeat the strategy if we are not in conflict.
      sentLemma = d_im.hasSentLemma();
      if (Trace.isOn("bags-check"))
      {
        // TODO: clean this Trace("bags-check") << "  ...finish run strategy: ";
        Trace("bags-check") << (hadPending ? "hadPending " : "");
        Trace("bags-check") << (sentLemma ? "sentLemma " : "");
        Trace("bags-check") << (d_state.isInConflict() ? "conflict " : "");
        if (!hadPending && !sentLemma && !d_state.isInConflict())
        {
          Trace("bags-check") << "(none)";
        }
        Trace("bags-check") << std::endl;
      }
      // repeat if we did not add a lemma or conflict, and we had pending
      // facts or lemmas.
    } while (!d_state.isInConflict() && !sentLemma && hadPending);
  }
  Trace("bags-check") << "Theory of bags, done check : " << effort << std::endl;
  Assert(!d_im.hasPendingFact());
  Assert(!d_im.hasPendingLemma());
}

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

void TheoryBags::eqNotifyNewClass(TNode t) { d_state.registerClass(t); }

void TheoryBags::eqNotifyMerge(TNode t1, TNode t2) {}

void TheoryBags::eqNotifyDisequal(TNode t1, TNode t2, TNode reason) {}

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
