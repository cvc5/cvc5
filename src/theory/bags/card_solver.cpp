/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Mathias Preiner, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Cardinality solver for theory of bags.
 */

#include "theory/bags/card_solver.h"

#include "expr/emptybag.h"
#include "smt/logic_exception.h"
#include "theory/bags/bags_utils.h"
#include "theory/bags/inference_generator.h"
#include "theory/bags/inference_manager.h"
#include "theory/bags/solver_state.h"
#include "theory/bags/term_registry.h"
#include "theory/uf/equality_engine_iterator.h"
#include "util/rational.h"

using namespace std;
using namespace cvc5::context;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace bags {

CardSolver::CardSolver(Env& env, SolverState& s, InferenceManager& im)
    : EnvObj(env), d_state(s), d_ig(&s, &im), d_im(im)
{
  d_nm = NodeManager::currentNM();
  d_zero = d_nm->mkConstInt(Rational(0));
  d_one = d_nm->mkConstInt(Rational(1));
  d_true = d_nm->mkConst(true);
  d_false = d_nm->mkConst(false);
}

CardSolver::~CardSolver() {}

void CardSolver::reset() { d_cardGraph.clear(); }

bool CardSolver::isLeaf(const Node& bag)
{
  Node rep = d_state.getRepresentative(bag);
  return (d_cardGraph.count(rep) == 0 || d_cardGraph[rep].empty());
}

std::set<Node> CardSolver::getChildren(Node bag)
{
  Node rep = d_state.getRepresentative(bag);
  if (d_cardGraph[rep].empty())
  {
    return {};
  }
  return *d_cardGraph[rep].begin();
}

void CardSolver::checkCardinalityGraph()
{
  const std::map<Node, Node>& cardinalityTerms = d_state.getCardinalityTerms();
  for (const auto& pair : cardinalityTerms)
  {
    Trace("bags-card") << "CardSolver::checkCardinalityGraph cardTerm: " << pair
                       << std::endl;
    Assert(pair.first.getKind() == BAG_CARD);
    Assert(d_state.hasTerm(pair.first[0]));
    Node bag = d_state.getRepresentative(pair.first[0]);
    Trace("bags-card") << "CardSolver::checkCardinalityGraph bag rep: " << bag
                       << std::endl;
    // enumerate all bag terms with bag operators
    eq::EqClassIterator it =
        eq::EqClassIterator(bag, d_state.getEqualityEngine());
    while (!it.isFinished())
    {
      Node n = (*it);
      Kind k = n.getKind();
      switch (k)
      {
        case BAG_EMPTY: checkEmpty(pair, n); break;
        case BAG_MAKE: checkBagMake(pair, n); break;
        case BAG_UNION_DISJOINT:
        {
          checkUnionDisjoint(pair, n);
          break;
        }
        case BAG_UNION_MAX: checkUnionMax(pair, n); break;
        case BAG_INTER_MIN: checkIntersectionMin(pair, n); break;
        case BAG_DIFFERENCE_SUBTRACT: checkDifferenceSubtract(pair, n); break;
        case BAG_DIFFERENCE_REMOVE: checkDifferenceRemove(pair, n); break;
        default: break;
      }
      if (d_im.hasSentLemma())
      {
        // exit with each new pending lemma
        return;
      }
      it++;
    }
    // if the bag is a leaf in the graph, then we reduce its cardinality
    checkLeafBag(pair, bag);
    // cardinality term is non-negative
    InferInfo i = d_ig.nonNegativeCardinality(pair.second);
    d_im.lemmaTheoryInference(&i);
  }
}

void CardSolver::checkEmpty(const std::pair<Node, Node>& pair, const Node& n)
{
  Assert(n.getKind() == BAG_EMPTY);
  InferInfo i = d_ig.cardEmpty(pair, n);
  d_im.lemmaTheoryInference(&i);
}

void CardSolver::checkBagMake(const std::pair<Node, Node>& pair, const Node& n)
{
  Assert(n.getKind() == BAG_MAKE);
  InferInfo i = d_ig.cardBagMake(pair, n);
  d_im.lemmaTheoryInference(&i);
}

void CardSolver::checkUnionDisjoint(const std::pair<Node, Node>& pair,
                                    const Node& n)
{
  Assert(n.getKind() == BAG_UNION_DISJOINT);
  Node bag = d_state.getRepresentative(pair.first[0]);
  Node A = d_state.getRepresentative(n[0]);
  Node B = d_state.getRepresentative(n[1]);
  addChildren(bag.eqNode(n), bag, {A, B});
}

void CardSolver::checkUnionMax(const std::pair<Node, Node>& pair, const Node& n)
{
  Assert(n.getKind() == BAG_UNION_MAX);
  Node bag = d_state.getRepresentative(pair.first[0]);
  Node A = d_state.getRepresentative(n[0]);
  Node B = d_state.getRepresentative(n[1]);
  Node subtractAB = d_nm->mkNode(BAG_DIFFERENCE_SUBTRACT, A, B);
  Node subtractBA = d_nm->mkNode(BAG_DIFFERENCE_SUBTRACT, B, A);
  // break the intersection symmetry using the node id
  Node interAB = A <= B ? d_nm->mkNode(BAG_INTER_MIN, A, B)
                        : d_nm->mkNode(BAG_INTER_MIN, B, A);
  Node subtractABRep = d_state.getRepresentative(subtractAB);
  Node subtractBARep = d_state.getRepresentative(subtractBA);
  Node interABRep = d_state.getRepresentative(interAB);
  addChildren(bag.eqNode(n), bag, {subtractABRep, interABRep, subtractBARep});
}

void CardSolver::addChildren(const Node& premise,
                             const Node& parent,
                             const set<Node>& children)
{
  if (children.count(parent) > 0 && children.size() > 1)
  {
    // handle the case when the parent is among the children, which implies
    // other children are empty.
    // This case is needed to avoid adding cycles in the cardinality graph
    std::vector<Node> emptyBags;
    Node empty = d_nm->mkConst(EmptyBag(parent.getType()));
    Trace("bags-card") << "CardSolver::addChildren parent: " << parent
                       << " is one of its children " << std::endl;
    for (Node child : children)
    {
      Trace("bags-card") << "CardSolver::addChildren child: " << child
                         << std::endl;
      if (child != parent)
      {
        // this child should be empty
        emptyBags.push_back(child.eqNode(empty));
      }
    }
    Trace("bags-card") << "CardSolver::addChildren empty bags: " << emptyBags
                       << std::endl;
    InferInfo i(&d_im, InferenceId::BAGS_CARD);
    i.d_premises.push_back(premise);
    if (emptyBags.size() == 1)
    {
      i.d_conclusion = *emptyBags.begin();
    }
    else
    {
      i.d_conclusion = d_nm->mkNode(AND, emptyBags);
    }
    Trace("bags-card") << "CardSolver::addChildren info: " << i << std::endl;
    d_im.lemmaTheoryInference(&i);
    return;
  }
  // add inferences
  InferInfo i = d_ig.cardUnionDisjoint(premise, parent, children);
  d_im.lemmaTheoryInference(&i);

  // make sure parent is in the graph
  if (d_cardGraph.count(parent) == 0)
  {
    d_cardGraph[parent] = {};
  }
  // make sure children are in the graph
  for (Node child : children)
  {
    if (d_cardGraph.count(child) == 0)
    {
      d_cardGraph[child] = {};
    }
  }

  // only add children if not in the graph
  if (d_cardGraph[parent].count(children) == 0)
  {
    if (d_cardGraph[parent].empty())
    {
      // The simple case is when the parent is a leaf in the cardinality graph.
      // This means we can just add the current set of children without
      // merging with a different set of children
      d_cardGraph[parent].insert(children);
    }
    else
    {
      // The hard case is when the parent is an internal node in the
      // cardinality graph, and has a different set of children.
      // In this case we reduce the cardinality of the parent bag using
      // quantifiers. This is faster than reducing the cardinality of each
      // child.
      const std::set<Node>& oldChildren = *d_cardGraph[parent].begin();
      d_cardGraph[parent].insert(children);
      Trace("bags-card") << "CardSolver::addChildren parent: " << parent
                         << std::endl;
      Trace("bags-card") << "CardSolver::addChildren set1: " << oldChildren
                         << std::endl;
      Trace("bags-card") << "CardSolver::addChildren set2: " << children
                         << std::endl;

      Node card = d_nm->mkNode(BAG_CARD, parent);
      std::vector<Node> asserts;
      Node reduced = BagReduction::reduceCardOperator(card, asserts);
      asserts.push_back(card.eqNode(reduced));
      InferInfo inferInfo(&d_im, InferenceId::BAGS_CARD);
      inferInfo.d_premises.push_back(premise);
      inferInfo.d_conclusion = d_nm->mkNode(AND, asserts);
      d_im.lemmaTheoryInference(&inferInfo);
    }
  }
}

void CardSolver::checkIntersectionMin(const std::pair<Node, Node>& pair,
                                      const Node& n)
{
  Assert(n.getKind() == BAG_INTER_MIN);
  Node bag = d_state.getRepresentative(pair.first[0]);
  Node A = d_state.getRepresentative(n[0]);
  Node B = d_state.getRepresentative(n[1]);
  Node subtractAB = d_nm->mkNode(BAG_DIFFERENCE_SUBTRACT, A, B);
  Node subtractBA = d_nm->mkNode(BAG_DIFFERENCE_SUBTRACT, B, A);
  // break the intersection symmetry using the node id
  Node interAB = A <= B ? d_nm->mkNode(BAG_INTER_MIN, A, B)
                        : d_nm->mkNode(BAG_INTER_MIN, B, A);
  Node subtractABRep = d_state.getRepresentative(subtractAB);
  Node subtractBARep = d_state.getRepresentative(subtractBA);
  Node interABRep = d_state.getRepresentative(interAB);
  addChildren(bag.eqNode(n), A, {subtractABRep, interABRep});
  addChildren(bag.eqNode(n), B, {interABRep, subtractBARep});
}

void CardSolver::checkDifferenceSubtract(const std::pair<Node, Node>& pair,
                                         const Node& n)
{
  Assert(n.getKind() == BAG_DIFFERENCE_SUBTRACT);
  Node bag = d_state.getRepresentative(pair.first[0]);
  Node A = d_state.getRepresentative(n[0]);
  Node B = d_state.getRepresentative(n[1]);
  // break the intersection symmetry using the node id
  Node interAB = A <= B ? d_nm->mkNode(BAG_INTER_MIN, A, B)
                        : d_nm->mkNode(BAG_INTER_MIN, B, A);
  Node interABRep = d_state.getRepresentative(interAB);
  addChildren(bag.eqNode(n), A, {bag, interABRep});
}

void CardSolver::checkDifferenceRemove(const std::pair<Node, Node>& pair,
                                       const Node& n)
{
  Assert(n.getKind() == BAG_DIFFERENCE_REMOVE);
  throw LogicException(
      "Cardinality for BAG_DIFFERENCE_REMOVE is not implemented yet");
}

void CardSolver::checkLeafBag(const std::pair<Node, Node>& pair,
                              const Node& bag)
{
  if (d_cardGraph[bag].size() == 0)
  {
    Trace("bags-card") << "Leaf: " << bag << std::endl;
    Trace("bags-card") << "cardTerm: " << pair << std::endl;
    const std::vector<std::pair<Node, Node>>& pairs =
        d_state.getElementCountPairs(bag);
    for (size_t i = 0; i < pairs.size(); i++)
    {
      Trace("bags-card") << "pair: " << pairs[i] << std::endl;
      bags::InferInfo inferInfo(&d_im, InferenceId::BAGS_CARD);
      Node leq = d_nm->mkNode(LEQ, pairs[i].second, pair.second);
      inferInfo.d_conclusion = leq;
      d_im.lemmaTheoryInference(&inferInfo);
      for (size_t j = i + 1; j < pairs.size(); j++)
      {
        std::vector<Node> distinct;
        std::vector<Node> counts;
        for (size_t k = 0; k < j; k++)
        {
          distinct.push_back(pairs[k].first.eqNode(pairs[j].first).notNode());
          counts.push_back(pairs[k].second);
        }
        counts.push_back(pairs[j].second);
        Node sum = d_nm->mkNode(ADD, counts);
        Node premise;
        if (distinct.size() == 1)
        {
          premise = distinct[0];
        }
        else
        {
          premise = d_nm->mkNode(AND, distinct);
        }
        bags::InferInfo sumInfo(&d_im, InferenceId::BAGS_CARD);
        Node sumLEQ = d_nm->mkNode(LEQ, sum, pair.second);
        sumInfo.d_conclusion = premise.negate().orNode(sumLEQ);
        d_im.lemmaTheoryInference(&sumInfo);
      }
    }
  }
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal
