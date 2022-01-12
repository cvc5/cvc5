/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Cardinality solver for theory of bags.
 */

#include "theory/bags/card_solver.h"

#include "expr/emptybag.h"
#include "theory/bags/inference_generator.h"
#include "theory/bags/inference_manager.h"
#include "theory/bags/normal_form.h"
#include "theory/bags/solver_state.h"
#include "theory/bags/term_registry.h"
#include "theory/uf/equality_engine_iterator.h"
#include "util/rational.h"

using namespace std;
using namespace cvc5::context;
using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace bags {

CardSolver::CardSolver(Env& env, SolverState& s, InferenceManager& im)
    : EnvObj(env), d_state(s), d_ig(&s, &im), d_im(im), d_bagReduction(env)
{
  d_zero = NodeManager::currentNM()->mkConstInt(Rational(0));
  d_one = NodeManager::currentNM()->mkConstInt(Rational(1));
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

CardSolver::~CardSolver() {}

void CardSolver::checkCardinalityGraph()
{
  for (const Node& cardTerm : d_state.getCardinalityTerms())
  {
    Trace("bags-card") << "cardTerm: " << cardTerm << std::endl;
    Assert(cardTerm.getKind() == BAG_CARD);
    Assert(d_state.hasTerm(cardTerm[0]));
    Node bag = d_state.getRepresentative(cardTerm[0]);
    Trace("bags-card") << "bag rep: " << bag << std::endl;
    // enumerate all bag terms with bag operators
    eq::EqClassIterator it =
        eq::EqClassIterator(bag, d_state.getEqualityEngine());
    while (!it.isFinished())
    {
      Node n = (*it);
      Kind k = n.getKind();
      Trace("bags-card") << "[" << bag << "] contains bag " << n << std::endl;
      switch (k)
      {
        case BAG_EMPTY: checkEmpty(cardTerm, n); break;
        case BAG_MAKE: checkBagMake(cardTerm, n); break;
        case BAG_UNION_DISJOINT:
        {
          checkUnionDisjoint(cardTerm, n);
          break;
        }
        case BAG_UNION_MAX: checkUnionMax(cardTerm, n); break;
        case BAG_INTER_MIN: checkIntersectionMin(cardTerm, n); break;
        case BAG_DIFFERENCE_SUBTRACT:
          checkDifferenceSubtract(cardTerm, n);
          break;
        case BAG_DIFFERENCE_REMOVE: checkDifferenceRemove(cardTerm, n); break;
        default: break;
      }
      it++;
    }
    // if the bag is a leaf in the graph, then we reduce its cardinality
    if (d_cardGraph.count(bag) == 0)
    {
      std::vector<Node> assertions;
      Node reduction = d_bagReduction.reduceCardOperator(cardTerm, assertions);
      assertions.push_back(reduction.eqNode(cardTerm));
      bags::InferInfo inferInfo(&d_im, InferenceId::BAGS_CARD);
      NodeManager* nm = NodeManager::currentNM();
      inferInfo.d_conclusion = nm->mkNode(AND, assertions);
      d_im.lemmaTheoryInference(&inferInfo);
    }
  }
}

void CardSolver::checkEmpty(const Node& cardTerm, const Node& n)
{
  Assert(n.getKind() == BAG_EMPTY);
  InferInfo i = d_ig.cardEmpty(cardTerm, n);
  d_im.lemmaTheoryInference(&i);
}

void CardSolver::checkBagMake(const Node& cardTerm, const Node& n)
{
  Assert(n.getKind() == BAG_MAKE);
  InferInfo i = d_ig.cardBagMake(cardTerm, n);
  d_im.lemmaTheoryInference(&i);
}

void CardSolver::checkUnionDisjoint(const Node& cardTerm, const Node& n)
{
  Assert(n.getKind() == BAG_UNION_DISJOINT);
  InferInfo i = d_ig.cardUnionDisjoint(cardTerm, n);
  d_im.lemmaTheoryInference(&i);
  Node bag = d_state.getRepresentative(cardTerm[0]);
  Node A = d_state.getRepresentative(n[0]);
  Node B = d_state.getRepresentative(n[1]);
  d_cardGraph[bag].insert({A, B});
  if (d_cardGraph.count(A) == 0)
  {
    d_cardGraph[A] = {};
  }
  if (d_cardGraph.count(B) == 0)
  {
    d_cardGraph[B] = {};
  }
}

void CardSolver::checkUnionMax(const Node& cardTerm, const Node& n)
{
  Assert(n.getKind() == BAG_UNION_MAX);
  Node bag = d_state.getRepresentative(cardTerm[0]);
  Node A = d_state.getRepresentative(n[0]);
  Node B = d_state.getRepresentative(n[1]);
  Node subtractAB = d_nm->mkNode(BAG_DIFFERENCE_SUBTRACT, A, B);
  Node subtractBA = d_nm->mkNode(BAG_DIFFERENCE_SUBTRACT, B, A);
  Node interAB = d_nm->mkNode(BAG_INTER_MIN, B, A);
  d_state.registerBag(subtractAB);
  d_state.registerBag(subtractBA);
  d_state.registerBag(interAB);
  Node subtractABRep = d_state.getRepresentative(subtractAB);
  Node subtractBARep = d_state.getRepresentative(subtractBA);
  Node interABRep = d_state.getRepresentative(interAB);
  addChildren(bag, {subtractAB, subtractBA, interAB});
  InferInfo i = d_ig.cardUnionMax(cardTerm, n, subtractAB, subtractBA, interAB);
  d_im.lemmaTheoryInference(&i);
}

void CardSolver::addChildren(const Node& parent, const set<Node>& children)
{
  d_cardGraph[parent].insert(children);
  for (Node child : children)
  {
    // if not in the graph
    if (d_cardGraph.count(child) == 0)
    {
      d_cardGraph[child] = {};
    }
  }
}

void CardSolver::checkIntersectionMin(const Node& cardTerm, const Node& n)
{
  Assert(n.getKind() == BAG_INTER_MIN);
}

void CardSolver::checkDifferenceSubtract(const Node& cardTerm, const Node& n)
{
  Assert(n.getKind() == BAG_DIFFERENCE_SUBTRACT);
}

void CardSolver::checkDifferenceRemove(const Node& cardTerm, const Node& n)
{
  Assert(n.getKind() == BAG_DIFFERENCE_REMOVE);
}

void CardSolver::reduceCardinality(const Node& cardTerm)
{
  std::vector<Node> asserts;
  Node ret = d_bagReduction.reduceCardOperator(cardTerm, asserts);
  NodeManager* nm = NodeManager::currentNM();
  Node equal = cardTerm.eqNode(ret);
  asserts.push_back(equal);
  Node andNode = nm->mkNode(AND, asserts);
  Trace("bags::ppr") << "reduce(" << cardTerm << ") = " << ret
                     << " such that:" << std::endl
                     << andNode << std::endl;
  d_im.lemma(andNode, InferenceId::BAGS_CARD);
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5
