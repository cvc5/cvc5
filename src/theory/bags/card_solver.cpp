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
  Trace("bags-card") << "-----------------------------------------"
                     << std::endl;
  Trace("bags-card") << "d_cardGraph :" << std::endl;
  for (const auto& pair : d_cardGraph)
  {
    Trace("bags-card") << pair.first << ": ";
    for (const auto& s : pair.second)
    {
      Trace("bags-card") << s << " ";
    }
    Trace("bags-card") << std::endl;
  }
  Trace("bags-card") << "-----------------------------------------"
                     << std::endl;
  if (d_cardGraph.count(rep) == 0 || d_cardGraph[rep].empty())
  {
    Trace("bags-card") << "isLeaf(" << rep << ") = true" << std::endl;
    return true;
  }
  Trace("bags-card") << "isLeaf(" << rep << ") = false" << std::endl;
  return false;
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
  generateRelatedCardinalityTerms();

  for (const auto& pair : d_state.getCardinalityTerms())
  {
    Trace("bags-card") << "cardTerm: " << pair << std::endl;
    Assert(pair.first.getKind() == BAG_CARD);
    Assert(d_state.hasTerm(pair.first[0]));
    Node bag = d_state.getRepresentative(pair.first[0]);
    Trace("bags-card") << "bag rep: " << bag << std::endl;
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
      it++;
    }
    // if the bag is a leaf in the graph, then we reduce its cardinality
    checkLeafBag(pair, bag);
  }

  for (const auto& pair : d_state.getCardinalityTerms())
  {
    InferInfo i = d_ig.nonNegativeCardinality(pair.second);
    d_im.lemmaTheoryInference(&i);
  }
}

void CardSolver::generateRelatedCardinalityTerms()
{
  const set<Node>& bags = d_state.getBags();
  for (const auto& pair : d_state.getCardinalityTerms())
  {
    Node rep = d_state.getRepresentative(pair.first[0]);
    Trace("bags-card") << "bag rep: " << rep << endl;
    // enumerate all bag terms that are related to the current bag
    for (const auto& bag : bags)
    {
      if (rep == bag)
      {
        continue;
      }
      eq::EqClassIterator it =
          eq::EqClassIterator(bag, d_state.getEqualityEngine());
      while (!it.isFinished())
      {
        Node n = (*it);
        Kind k = n.getKind();
        switch (k)
        {
          case BAG_EMPTY: break;
          case BAG_MAKE: break;
          case BAG_UNION_DISJOINT:
          {
            Node A = d_state.getRepresentative(n[0]);
            Node B = d_state.getRepresentative(n[1]);
            if (A == rep || B == rep)
            {
              d_state.registerCardinalityTerm(d_nm->mkNode(BAG_CARD, A));
              d_state.registerCardinalityTerm(d_nm->mkNode(BAG_CARD, B));
              d_state.registerCardinalityTerm(d_nm->mkNode(BAG_CARD, n));
            }
            break;
          }
          case BAG_UNION_MAX:
          {
            Node A = d_state.getRepresentative(n[0]);
            Node B = d_state.getRepresentative(n[1]);
            if (A == rep || B == rep)
            {
              d_state.registerCardinalityTerm(d_nm->mkNode(BAG_CARD, A));
              d_state.registerCardinalityTerm(d_nm->mkNode(BAG_CARD, B));
              d_state.registerCardinalityTerm(d_nm->mkNode(BAG_CARD, n));
              // break the intersection symmetry using the node id
              Node inter = A <= B ? d_nm->mkNode(BAG_INTER_MIN, A, B)
                                  : d_nm->mkNode(BAG_INTER_MIN, B, A);
              Node subtractAB =
                  d_nm->mkNode(kind::BAG_DIFFERENCE_SUBTRACT, A, B);
              Node subtractBA =
                  d_nm->mkNode(kind::BAG_DIFFERENCE_SUBTRACT, B, A);
              d_state.registerBag(inter);
              d_state.registerBag(subtractAB);
              d_state.registerBag(subtractBA);
              d_state.registerCardinalityTerm(d_nm->mkNode(BAG_CARD, inter));
              d_state.registerCardinalityTerm(
                  d_nm->mkNode(BAG_CARD, subtractAB));
              d_state.registerCardinalityTerm(
                  d_nm->mkNode(BAG_CARD, subtractBA));
            }
            break;
          }
          case BAG_INTER_MIN: break;
          case BAG_DIFFERENCE_SUBTRACT:
          {
            Node A = d_state.getRepresentative(n[0]);
            Node B = d_state.getRepresentative(n[1]);
            if (A == rep || B == rep)
            {
              d_state.registerCardinalityTerm(d_nm->mkNode(BAG_CARD, A));
              d_state.registerCardinalityTerm(d_nm->mkNode(BAG_CARD, B));
              d_state.registerCardinalityTerm(d_nm->mkNode(BAG_CARD, n));
              // break the intersection symmetry using the node id
              Node inter = A <= B ? d_nm->mkNode(BAG_INTER_MIN, A, B)
                                  : d_nm->mkNode(BAG_INTER_MIN, B, A);
              d_state.registerBag(inter);
              d_state.registerCardinalityTerm(d_nm->mkNode(BAG_CARD, inter));
            }
            break;
          }
          case BAG_DIFFERENCE_REMOVE: break;
          default: break;
        }
        it++;
      }
    }
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
  InferInfo i = d_ig.cardUnionDisjoint(pair, n);
  d_im.lemmaTheoryInference(&i);
  Node bag = d_state.getRepresentative(pair.first[0]);
  Node A = d_state.getRepresentative(n[0]);
  Node B = d_state.getRepresentative(n[1]);
  addChildren(bag, {A, B});
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
  d_state.registerBag(subtractAB);
  d_state.registerBag(subtractBA);
  d_state.registerBag(interAB);
  Node subtractABRep = d_state.getRepresentative(subtractAB);
  Node subtractBARep = d_state.getRepresentative(subtractBA);
  Node interABRep = d_state.getRepresentative(interAB);
  addChildren(bag, {subtractABRep, interABRep, subtractBARep});
  InferInfo i = d_ig.cardUnionMax(pair, n, subtractAB, subtractBA, interAB);
  d_im.lemmaTheoryInference(&i);
}

void CardSolver::addChildren(const Node& parent, const set<Node>& children)
{
  // make sure parent is in the graph
  if (d_cardGraph.count(parent) == 0)
  {
    d_cardGraph[parent] = {};
  }
  // make sure children are in the graph
  for (Node child : children)
  {
    // if not in the graph
    if (d_cardGraph.count(child) == 0)
    {
      d_cardGraph[child] = {};
    }
  }

  if (d_cardGraph[parent].count(children) == 0)
  {
    if (d_cardGraph[parent].size() == 0)
    {
      d_cardGraph[parent].insert(children);
    }
    else
    {
      // merge with the first set
      const std::set<Node>& oldChildren = *d_cardGraph[parent].begin();
      d_cardGraph[parent].insert(children);
      mergeChildren(oldChildren, children);
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
  d_state.registerBag(subtractAB);
  d_state.registerBag(subtractBA);
  d_state.registerBag(interAB);
  Node subtractABRep = d_state.getRepresentative(subtractAB);
  Node subtractBARep = d_state.getRepresentative(subtractBA);
  Node interABRep = d_state.getRepresentative(interAB);
  addChildren(A, {subtractABRep, interABRep});
  addChildren(B, {interABRep, subtractBARep});
  InferInfo i =
      d_ig.cardIntersectionMin(pair, n, subtractAB, subtractBA, interAB);
  d_im.lemmaTheoryInference(&i);
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
  d_state.registerBag(interAB);
  Node interABRep = d_state.getRepresentative(interAB);
  addChildren(A, {bag, interABRep});
}

void CardSolver::checkDifferenceRemove(const std::pair<Node, Node>& pair,
                                       const Node& n)
{
  Assert(n.getKind() == BAG_DIFFERENCE_REMOVE);
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
        Node sum = d_nm->mkNode(PLUS, counts);
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

void CardSolver::mergeChildren(const set<Node>& set1, const set<Node>& set2)
{
  Trace("bags-card") << "CardSolver::mergeChildren set1: " << set1 << std::endl;
  Trace("bags-card") << "CardSolver::mergeChildren set2: " << set2 << std::endl;
  std::set<Node> leaves1 = getLeaves(set1);
  Trace("bags-card") << "leaves1: " << leaves1 << std::endl;
  std::set<Node> leaves2 = getLeaves(set2);
  Trace("bags-card") << "leaves2: " << leaves2 << std::endl;

  for (Node n1 : leaves1)
  {
    std::set<Node> children;
    for (Node n2 : leaves2)
    {
      Node inter = n1 <= n2 ? d_nm->mkNode(BAG_INTER_MIN, n1, n2)
                            : d_nm->mkNode(BAG_INTER_MIN, n2, n1);
      d_state.registerBag(inter);
      Node rep = d_state.getRepresentative(inter);
      children.insert(rep);
    }
    Trace("bags-card") << "new leaves: " << children << std::endl;
  }
}
std::set<Node> CardSolver::getLeaves(const set<Node>& set)
{
  std::set<Node> leaves;
  for (Node n : set)
  {
    if (d_cardGraph[n].empty())
    {
      leaves.insert(n);
    }
  }
  return leaves;
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5
