/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bags theory.
 */

#include "theory/bags/theory_bags.h"

#include "expr/emptybag.h"
#include "expr/skolem_manager.h"
#include "proof/proof_checker.h"
#include "smt/logic_exception.h"
#include "theory/bags/bags_utils.h"
#include "theory/quantifiers/fmf/bounded_integers.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace bags {

TheoryBags::TheoryBags(Env& env, OutputChannel& out, Valuation valuation)
    : Theory(THEORY_BAGS, env, out, valuation),
      d_state(env, valuation),
      d_im(env, *this, d_state),
      d_ig(&d_state, &d_im),
      d_notify(*this, d_im),
      d_statistics(statisticsRegistry()),
      d_rewriter(env.getRewriter(), &d_statistics.d_rewrites),
      d_termReg(env, d_state, d_im),
      d_solver(env, d_state, d_im, d_termReg),
      d_cardSolver(env, d_state, d_im),
      d_cpacb(*this)
{
  // use the official theory state and inference manager objects
  d_theoryState = &d_state;
  d_inferManager = &d_im;
}

TheoryBags::~TheoryBags() {}

TheoryRewriter* TheoryBags::getTheoryRewriter() { return &d_rewriter; }

ProofRuleChecker* TheoryBags::getProofChecker() { return nullptr; }

bool TheoryBags::needsEqualityEngine(EeSetupInfo& esi)
{
  esi.d_notify = &d_notify;
  esi.d_name = "theory::bags::ee";
  return true;
}

void TheoryBags::finishInit()
{
  Assert(d_equalityEngine != nullptr);

  d_valuation.setUnevaluatedKind(WITNESS);

  // functions we are doing congruence over
  d_equalityEngine->addFunctionKind(BAG_UNION_MAX);
  d_equalityEngine->addFunctionKind(BAG_UNION_DISJOINT);
  d_equalityEngine->addFunctionKind(BAG_INTER_MIN);
  d_equalityEngine->addFunctionKind(BAG_DIFFERENCE_SUBTRACT);
  d_equalityEngine->addFunctionKind(BAG_DIFFERENCE_REMOVE);
  d_equalityEngine->addFunctionKind(BAG_COUNT);
  d_equalityEngine->addFunctionKind(BAG_DUPLICATE_REMOVAL);
  d_equalityEngine->addFunctionKind(BAG_MAKE);
  d_equalityEngine->addFunctionKind(BAG_CARD);
  d_equalityEngine->addFunctionKind(BAG_FROM_SET);
  d_equalityEngine->addFunctionKind(BAG_TO_SET);
  d_equalityEngine->addFunctionKind(BAG_PARTITION);
  d_equalityEngine->addFunctionKind(TABLE_PRODUCT);
  d_equalityEngine->addFunctionKind(TABLE_PROJECT);
  d_equalityEngine->addFunctionKind(TABLE_AGGREGATE);
  d_equalityEngine->addFunctionKind(TABLE_JOIN);
  d_equalityEngine->addFunctionKind(TABLE_GROUP);
}

TrustNode TheoryBags::ppRewrite(TNode atom, std::vector<SkolemLemma>& lems)
{
  Trace("bags-ppr") << "TheoryBags::ppRewrite " << atom << std::endl;

  switch (atom.getKind())
  {
    case kind::BAG_CHOOSE: return expandChooseOperator(atom, lems);
    case kind::BAG_FOLD:
    {
      std::vector<Node> asserts;
      Node ret = BagReduction::reduceFoldOperator(atom, asserts);
      NodeManager* nm = NodeManager::currentNM();
      Node andNode = nm->mkNode(AND, asserts);
      d_im.lemma(andNode, InferenceId::BAGS_FOLD);
      Trace("bags::ppr") << "reduce(" << atom << ") = " << ret
                         << " such that:" << std::endl
                         << andNode << std::endl;
      return TrustNode::mkTrustRewrite(atom, ret, nullptr);
    }
    case kind::TABLE_AGGREGATE:
    {
      Node ret = BagReduction::reduceAggregateOperator(atom);
      Trace("bags::ppr") << "reduce(" << atom << ") = " << ret << std::endl;
      return TrustNode::mkTrustRewrite(atom, ret, nullptr);
    }
    case kind::TABLE_PROJECT:
    {
      Node ret = BagReduction::reduceProjectOperator(atom);
      Trace("bags::ppr") << "reduce(" << atom << ") = " << ret << std::endl;
      return TrustNode::mkTrustRewrite(atom, ret, nullptr);
    }
    default: return TrustNode::null();
  }
}

TrustNode TheoryBags::expandChooseOperator(const Node& node,
                                           std::vector<SkolemLemma>& lems)
{
  Assert(node.getKind() == BAG_CHOOSE);

  // (bag.choose A) is eliminated to k, with lemma
  // (and (= k (uf A)) (or (= A (as bag.empty (Bag E))) (>= (bag.count k A) 1)))
  // where uf: (Bag E) -> E is a skolem function, and E is the type of elements
  // of A

  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  Node x = sm->mkPurifySkolem(node);
  Node A = node[0];
  TypeNode bagType = A.getType();
  TypeNode ufType = nm->mkFunctionType(bagType, bagType.getBagElementType());
  // a Null node is used here to get a unique skolem function per bag type
  Node uf = sm->mkSkolemFunction(SkolemFunId::BAGS_CHOOSE, ufType, Node());
  Node ufA = NodeManager::currentNM()->mkNode(APPLY_UF, uf, A);

  Node equal = x.eqNode(ufA);
  Node emptyBag = nm->mkConst(EmptyBag(bagType));
  Node isEmpty = A.eqNode(emptyBag);
  Node count = nm->mkNode(BAG_COUNT, x, A);
  Node one = nm->mkConstInt(Rational(1));
  Node geqOne = nm->mkNode(GEQ, count, one);
  Node lem = nm->mkNode(AND, equal, nm->mkNode(OR, isEmpty, geqOne));
  TrustNode tlem = TrustNode::mkTrustLemma(lem, nullptr);
  lems.push_back(SkolemLemma(tlem, x));
  Trace("TheoryBags::ppRewrite")
      << "ppRewrite(" << node << ") = " << x << std::endl;
  return TrustNode::mkTrustRewrite(node, x, nullptr);
}

void TheoryBags::initialize()
{
  d_state.reset();
  d_opMap.clear();
  d_state.collectDisequalBagTerms();
  collectBagsAndCountTerms();
}

void TheoryBags::collectBagsAndCountTerms()
{
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  eq::EqClassesIterator repIt = eq::EqClassesIterator(ee);
  while (!repIt.isFinished())
  {
    Node eqc = (*repIt);
    Trace("bags-eqc") << "Eqc [ " << eqc << " ] = { ";

    if (eqc.getType().isBag())
    {
      d_state.registerBag(eqc);
    }

    eq::EqClassIterator it = eq::EqClassIterator(eqc, ee);
    while (!it.isFinished())
    {
      Node n = (*it);
      d_opMap[n.getKind()].push_back(n);
      Trace("bags-eqc") << (*it) << " ";
      Kind k = n.getKind();
      if (k == BAG_MAKE)
      {
        // for terms (bag x c) we need to store x by registering the count term
        // (bag.count x (bag x c))
        NodeManager* nm = NodeManager::currentNM();
        Node count = nm->mkNode(BAG_COUNT, n[0], n);
        d_ig.registerCountTerm(count);
      }
      if (k == BAG_COUNT)
      {
        // this takes care of all count terms in each equivalent class
        d_ig.registerCountTerm(n);
      }
      if (k == BAG_CARD)
      {
        d_ig.registerCardinalityTerm(n);
      }
      if (k == TABLE_GROUP)
      {
        d_state.registerGroupTerm(n);
      }
      ++it;
    }
    Trace("bags-eqc") << " } " << std::endl;
    ++repIt;
  }
}

void TheoryBags::postCheck(Effort effort)
{
  d_im.doPendingFacts();
  Assert(d_strat.isStrategyInit());
  if (!d_state.isInConflict() && !d_valuation.needCheck()
      && d_strat.hasStrategyEffort(effort))
  {
    Trace("bags::TheoryBags::postCheck") << "effort: " << effort << std::endl;

    // TODO issue #78: add ++(d_statistics.d_checkRuns);
    bool sentLemma = false;
    bool hadPending = false;
    Trace("bags-check") << "Full effort check..." << std::endl;
    do
    {
      d_im.reset();
      // TODO issue #78: add ++(d_statistics.d_strategyRuns);
      Trace("bags-check") << "  * Run strategy..." << std::endl;
      initialize();
      d_cardSolver.reset();
      runStrategy(effort);

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
      if (TraceIsOn("bags-check"))
      {
        Trace("bags-check") << "  ...finish run strategy: ";
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

void TheoryBags::runStrategy(Theory::Effort e)
{
  std::vector<std::pair<InferStep, size_t>>::iterator it = d_strat.stepBegin(e);
  std::vector<std::pair<InferStep, size_t>>::iterator stepEnd =
      d_strat.stepEnd(e);

  Trace("bags-process") << "----check, next round---" << std::endl;
  while (it != stepEnd)
  {
    InferStep curr = it->first;
    if (curr == BREAK)
    {
      if (d_state.isInConflict() || d_im.hasPending())
      {
        break;
      }
    }
    else
    {
      if (runInferStep(curr, it->second) || d_state.isInConflict())
      {
        break;
      }
    }
    ++it;
  }
  Trace("bags-process") << "----finished round---" << std::endl;
}

/** run the given inference step */
bool TheoryBags::runInferStep(InferStep s, int effort)
{
  Trace("bags-process") << "Run " << s;
  if (effort > 0)
  {
    Trace("bags-process") << ", effort = " << effort;
  }
  Trace("bags-process") << "..." << std::endl;
  switch (s)
  {
    case CHECK_INIT: break;
    case CHECK_BAG_MAKE:
    {
      if (d_solver.checkBagMake())
      {
        return true;
      }
      break;
    }
    case CHECK_BASIC_OPERATIONS: d_solver.checkBasicOperations(); break;
    case CHECK_CARDINALITY_CONSTRAINTS:
      d_cardSolver.checkCardinalityGraph();
      break;
    default: Unreachable(); break;
  }
  Trace("bags-process") << "Done " << s
                        << ", addedFact = " << d_im.hasPendingFact()
                        << ", addedLemma = " << d_im.hasPendingLemma()
                        << ", conflict = " << d_state.isInConflict()
                        << std::endl;
  return false;
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

  // a map from bag representatives to their constructed values
  std::map<Node, Node> processedBags;

  // get the relevant bag equivalence classes
  for (const Node& n : termSet)
  {
    TypeNode tn = n.getType();
    if (!tn.isBag())
    {
      // we are only concerned here about bag terms
      continue;
    }
    Node r = d_state.getRepresentative(n);

    if (processedBags.find(r) != processedBags.end())
    {
      // skip bags whose representatives are already processed
      continue;
    }

    const std::vector<std::pair<Node, Node>>& solverElements =
        d_state.getElementCountPairs(r);
    std::vector<std::pair<Node, Node>> elements;
    for (std::pair<Node, Node> pair : solverElements)
    {
      if (termSet.find(pair.first) == termSet.end())
      {
        continue;
      }
      elements.push_back(pair);
    }

    std::map<Node, Node> elementReps;
    for (std::pair<Node, Node> pair : elements)
    {
      Node key = d_state.getRepresentative(pair.first);
      Node countSkolem = pair.second;
      Node value = m->getRepresentative(countSkolem);
      elementReps[key] = value;
    }
    Node constructedBag = BagsUtils::constructBagFromElements(tn, elementReps);
    constructedBag = rewrite(constructedBag);
    NodeManager* nm = NodeManager::currentNM();
    if (d_state.hasCardinalityTerms())
    {
      if (d_cardSolver.isLeaf(n))
      {
        Node constructedBagCard = rewrite(nm->mkNode(BAG_CARD, constructedBag));
        Trace("bags-model")
            << "constructed bag cardinality: " << constructedBagCard
            << std::endl;
        Node rCard = nm->mkNode(BAG_CARD, r);
        Node rCardSkolem = d_state.getCardinalitySkolem(rCard);
        Trace("bags-model") << "rCardSkolem : " << rCardSkolem << std::endl;
        if (!rCardSkolem.isNull())
        {
          Node rCardModelValue = m->getRepresentative(rCardSkolem);
          const Rational& rCardRational = rCardModelValue.getConst<Rational>();
          const Rational& constructedRational =
              constructedBagCard.getConst<Rational>();
          Trace("bags-model")
              << "constructedRational : " << constructedRational << std::endl;
          Trace("bags-model")
              << "rCardRational : " << rCardRational << std::endl;
          Assert(constructedRational <= rCardRational);
          TypeNode elementType = r.getType().getBagElementType();
          if (constructedRational < rCardRational
              && !d_env.isFiniteType(elementType))
          {
            Node newElement =
                nm->getSkolemManager()->mkDummySkolem("slack", elementType);
            Trace("bags-model") << "newElement is " << newElement << std::endl;
            Rational difference = rCardRational - constructedRational;
            Node multiplicity = nm->mkConstInt(difference);
            Node slackBag = nm->mkNode(BAG_MAKE, newElement, multiplicity);
            constructedBag =
                nm->mkNode(kind::BAG_UNION_DISJOINT, constructedBag, slackBag);
            constructedBag = rewrite(constructedBag);
          }
        }
      }
      else
      {
        std::set<Node> children = d_cardSolver.getChildren(n);
        Assert(!children.empty());
        constructedBag = nm->mkConst(EmptyBag(r.getType()));
        for (Node child : children)
        {
          Trace("bags-model")
              << "child bag for " << n << " is: " << child << std::endl;
          constructedBag =
              nm->mkNode(BAG_UNION_DISJOINT, child, constructedBag);
        }
        constructedBag = rewrite(constructedBag);
        Trace("bags-model") << "constructed bag for " << n
                            << " is: " << constructedBag << std::endl;
      }
    }
    m->assertEquality(constructedBag, n, true);
    m->assertSkeleton(constructedBag);
    processedBags[r] = constructedBag;
  }

  Trace("bags-model") << "processedBags:  " << processedBags << std::endl;
  return true;
}

TrustNode TheoryBags::explain(TNode node) { return d_im.explainLit(node); }

Node TheoryBags::getCandidateModelValue(TNode node) { return Node::null(); }

void TheoryBags::preRegisterTerm(TNode n)
{
  Trace("bags") << "TheoryBags::preRegisterTerm(" << n << ")" << std::endl;
  switch (n.getKind())
  {
    case kind::EQUAL:
    {
      // add trigger predicate for equality and membership
      d_state.addEqualityEngineTriggerPredicate(n);
    }
    break;
    case BAG_FROM_SET:
    case BAG_TO_SET:
    case BAG_IS_SINGLETON:
    case BAG_PARTITION:
    {
      std::stringstream ss;
      ss << "Term of kind " << n.getKind() << " is not supported yet";
      throw LogicException(ss.str());
    }
    default: d_equalityEngine->addTerm(n); break;
  }
}

void TheoryBags::presolve()
{
  Trace("bags-presolve") << "Started presolve" << std::endl;
  d_strat.initializeStrategy();
  Trace("bags-presolve") << "Finished presolve" << std::endl;
}

/**************************** eq::NotifyClass *****************************/

void TheoryBags::eqNotifyNewClass(TNode n) {}

void TheoryBags::eqNotifyMerge(TNode n1, TNode n2) {}

void TheoryBags::eqNotifyDisequal(TNode n1, TNode n2, TNode reason) {}

void TheoryBags::NotifyClass::eqNotifyNewClass(TNode n)
{
  Trace("bags-eq") << "[bags-eq] eqNotifyNewClass:"
                   << " n = " << n << std::endl;
  d_theory.eqNotifyNewClass(n);
}

void TheoryBags::NotifyClass::eqNotifyMerge(TNode n1, TNode n2)
{
  Trace("bags-eq") << "[bags-eq] eqNotifyMerge:"
                   << " n1 = " << n1 << " n2 = " << n2 << std::endl;
  d_theory.eqNotifyMerge(n1, n2);
}

void TheoryBags::NotifyClass::eqNotifyDisequal(TNode n1, TNode n2, TNode reason)
{
  Trace("bags-eq") << "[bags-eq] eqNotifyDisequal:"
                   << " n1 = " << n1 << " n2 = " << n2 << " reason = " << reason
                   << std::endl;
  d_theory.eqNotifyDisequal(n1, n2, reason);
}

bool TheoryBags::isCareArg(Node n, unsigned a)
{
  if (d_equalityEngine->isTriggerTerm(n[a], THEORY_BAGS))
  {
    return true;
  }
  else if ((n.getKind() == kind::BAG_COUNT || n.getKind() == kind::BAG_MAKE)
           && a == 0 && n[0].getType().isBag())
  {
    // when the elements themselves are bags
    return true;
  }
  return false;
}

void TheoryBags::computeCareGraph()
{
  Trace("bags-cg") << "Compute graph for bags" << std::endl;
  for (const std::pair<const Kind, std::vector<Node>>& it : d_opMap)
  {
    Kind k = it.first;
    if (k == kind::BAG_MAKE || k == kind::BAG_COUNT)
    {
      Trace("bags-cg") << "kind: " << k << ", size = " << it.second.size()
                       << std::endl;
      std::map<TypeNode, TNodeTrie> index;
      unsigned arity = 0;
      // populate indices
      for (TNode n : it.second)
      {
        Trace("bags-cg") << "computing n:  " << n << std::endl;
        Assert(d_equalityEngine->hasTerm(n));
        TypeNode tn;
        if (k == kind::BAG_MAKE)
        {
          tn = n.getType().getBagElementType();
        }
        else
        {
          Assert(k == kind::BAG_COUNT);
          tn = n[1].getType().getBagElementType();
        }
        std::vector<TNode> childrenReps;
        bool hasCareArg = false;
        for (unsigned j = 0; j < n.getNumChildren(); j++)
        {
          childrenReps.push_back(d_equalityEngine->getRepresentative(n[j]));
          if (isCareArg(n, j))
          {
            hasCareArg = true;
          }
        }
        if (hasCareArg)
        {
          Trace("bags-cg") << "addTerm(" << n << ", " << childrenReps << ")"
                           << std::endl;
          index[tn].addTerm(n, childrenReps);
          arity = childrenReps.size();
        }
        else
        {
          Trace("bags-cg") << "......skip." << std::endl;
        }
      }
      if (arity > 0)
      {
        // for each index
        for (std::pair<const TypeNode, TNodeTrie>& tt : index)
        {
          Trace("bags-cg") << "Process index " << tt.first << "..."
                           << std::endl;
          nodeTriePathPairProcess(&tt.second, arity, d_cpacb);
        }
      }
      Trace("bags-cg") << "...done" << std::endl;
    }
  }
}

void TheoryBags::processCarePairArgs(TNode a, TNode b)
{
  // we care about the equality or disequality between x, y
  // when (bag.count x A) = (bag.count y A)
  if (a.getKind() != BAG_COUNT && d_state.areEqual(a, b))
  {
    return;
  }
  // otherwise, we add pairs for each of their arguments
  addCarePairArgs(a, b);
  size_t childrenSize = a.getNumChildren();
  for (size_t i = 0; i < childrenSize; ++i)
  {
    TNode x = a[i];
    TNode y = b[i];
    if (!d_equalityEngine->areEqual(x, y))
    {
      if (isCareArg(a, i) && isCareArg(b, i))
      {
        // splitting on bags (necessary for handling bag of bags properly)
        if (x.getType().isBag())
        {
          Assert(y.getType().isBag());
          Trace("bags-cg-lemma")
              << "Should split on : " << x << "==" << y << std::endl;
          Node equal = x.eqNode(y);
          Node lemma = equal.orNode(equal.notNode());
          d_im.lemma(lemma, InferenceId::BAGS_CG_SPLIT);
        }
      }
    }
  }
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal
