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

#include "theory/theory_model.h"

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
      d_ig(&d_state),
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
  // TODO issue #78: add Assert(d_strat.isStrategyInit());
  if (!d_state.isInConflict() && !d_valuation.needCheck())
  // TODO issue #78:  add && d_strat.hasStrategyEffort(e))
  {
    Trace("bags::TheoryBags::postCheck") << "effort: " << std::endl;

    // TODO issue #78: add ++(d_statistics.d_checkRuns);
    bool sentLemma = false;
    bool hadPending = false;
    Trace("bags-check") << "Full effort check..." << std::endl;
    do
    {
      d_im.reset();
      // TODO issue #78: add ++(d_statistics.d_strategyRuns);
      Trace("bags-check") << "  * Run strategy..." << std::endl;
      // TODO issue #78: add runStrategy(e);

      d_solver.postCheck();

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
                                    const std::set<Node>& termSet)
{
  Trace("bags-model") << "TheoryBags : Collect model values" << std::endl;

  Trace("bags-model") << "Term set: " << termSet << std::endl;

  // get the relevant bag equivalence classes
  for (const Node& n : termSet)
  {
    TypeNode tn = n.getType();
    if (!tn.isBag())
    {
      continue;
    }
    Node r = d_state.getRepresentative(n);
    std::set<Node> solverElements = d_state.getElements(r);
    std::set<Node> elements;
    // only consider terms in termSet and ignore other elements in the solver
    std::set_intersection(termSet.begin(),
                          termSet.end(),
                          solverElements.begin(),
                          solverElements.end(),
                          std::inserter(elements, elements.begin()));
    Trace("bags-model") << "Elements of bag " << n << " are: " << std::endl
                        << elements << std::endl;
    std::map<Node, Node> elementReps;
    for (const Node& e : elements)
    {
      Node key = d_state.getRepresentative(e);
      Node countTerm = NodeManager::currentNM()->mkNode(BAG_COUNT, e, r);
      Node value = d_state.getRepresentative(countTerm);
      elementReps[key] = value;
    }
    Node rep = NormalForm::constructBagFromElements(tn, elementReps);
    rep = Rewriter::rewrite(rep);

    Trace("bags-model") << "rep of " << n << " is: " << rep << std::endl;
    for (std::pair<Node, Node> pair : elementReps)
    {
      m->assertSkeleton(pair.first);
      m->assertSkeleton(pair.second);
    }
    m->assertEquality(rep, n, true);
    m->assertSkeleton(rep);
  }
  return true;
}

TrustNode TheoryBags::explain(TNode node) { return d_im.explainLit(node); }

Node TheoryBags::getModelValue(TNode node) { return Node::null(); }

void TheoryBags::preRegisterTerm(TNode n)
{
  Trace("bags::TheoryBags::preRegisterTerm") << n << std::endl;
  switch (n.getKind())
  {
    case BAG_CARD:
    case BAG_FROM_SET:
    case BAG_TO_SET:
    case BAG_IS_SINGLETON:
    case DUPLICATE_REMOVAL:
    {
      std::stringstream ss;
      ss << "Term of kind " << n.getKind() << " is not supported yet";
      throw LogicException(ss.str());
    }
    default: break;
  }
}

TrustNode TheoryBags::expandDefinition(Node n)
{
  // TODO(projects#224): add choose and is_singleton here
  return TrustNode::null();
}

void TheoryBags::presolve() {}

/**************************** eq::NotifyClass *****************************/

void TheoryBags::eqNotifyNewClass(TNode n) {}

void TheoryBags::eqNotifyMerge(TNode n1, TNode n2) {}

void TheoryBags::eqNotifyDisequal(TNode n1, TNode n2, TNode reason)
{
  TypeNode t1 = n1.getType();
  if (t1.isBag())
  {
    InferInfo info = d_ig.bagDisequality(n1.eqNode(n2).notNode(), reason);
    info.process(d_inferManager, true);
  }
}

void TheoryBags::NotifyClass::eqNotifyNewClass(TNode n)
{
  Debug("bags-eq") << "[bags-eq] eqNotifyNewClass:"
                   << " n = " << n << std::endl;
  d_theory.eqNotifyNewClass(n);
}

void TheoryBags::NotifyClass::eqNotifyMerge(TNode n1, TNode n2)
{
  Debug("bags-eq") << "[bags-eq] eqNotifyMerge:"
                   << " n1 = " << n1 << " n2 = " << n2 << std::endl;
  d_theory.eqNotifyMerge(n1, n2);
}

void TheoryBags::NotifyClass::eqNotifyDisequal(TNode n1, TNode n2, TNode reason)
{
  Debug("bags-eq") << "[bags-eq] eqNotifyDisequal:"
                   << " n1 = " << n1 << " n2 = " << n2 << " reason = " << reason
                   << std::endl;
  d_theory.eqNotifyDisequal(n1, n2, reason);
}

}  // namespace bags
}  // namespace theory
}  // namespace CVC4
