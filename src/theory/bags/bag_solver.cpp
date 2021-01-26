/*********************                                                        */
/*! \file bag_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief solver for the theory of bags.
 **
 ** solver for the theory of bags.
 **/

#include "theory/bags/bag_solver.h"

#include "theory/bags/inference_generator.h"

using namespace std;
using namespace CVC4::context;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace bags {

BagSolver::BagSolver(SolverState& s, InferenceManager& im, TermRegistry& tr)
    : d_state(s), d_im(im), d_termReg(tr)
{
  d_zero = NodeManager::currentNM()->mkConst(Rational(0));
  d_one = NodeManager::currentNM()->mkConst(Rational(1));
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

BagSolver::~BagSolver() {}

void BagSolver::postCheck()
{
  d_state.initialize();

  // At this point, all bag and count representatives should be in the solver
  // state.
  for (const Node& bag : d_state.getBags())
  {
    // iterate through all bags terms in each equivalent class
    eq::EqClassIterator it =
        eq::EqClassIterator(bag, d_state.getEqualityEngine());
    while (!it.isFinished())
    {
      Node n = (*it);
      Kind k = n.getKind();
      switch (k)
      {
        case kind::MK_BAG: checkMkBag(n); break;
        case kind::UNION_DISJOINT: checkUnionDisjoint(n); break;
        case kind::UNION_MAX: checkUnionMax(n); break;
        case kind::DIFFERENCE_SUBTRACT: checkDifferenceSubtract(n); break;
        case kind::DIFFERENCE_REMOVE: checkDifferenceRemove(n); break;
        default: break;
      }
      it++;
    }
  }

  // add non negative constraints for all multiplicities
  for (const Node& n : d_state.getBags())
  {
    for (const Node& e : d_state.getElements(n))
    {
      checkNonNegativeCountTerms(n, e);
    }
  }
}

set<Node> BagSolver::getElementsForBinaryOperator(const Node& n)
{
  set<Node> elements;
  const set<Node>& downwards = d_state.getElements(n);
  const set<Node>& upwards0 = d_state.getElements(n[0]);
  const set<Node>& upwards1 = d_state.getElements(n[1]);

  set_union(downwards.begin(),
            downwards.end(),
            upwards0.begin(),
            upwards0.end(),
            inserter(elements, elements.begin()));
  elements.insert(upwards1.begin(), upwards1.end());
  return elements;
}

void BagSolver::checkUnionDisjoint(const Node& n)
{
  Assert(n.getKind() == UNION_DISJOINT);
  std::set<Node> elements = getElementsForBinaryOperator(n);
  for (const Node& e : elements)
  {
    InferenceGenerator ig(&d_state);
    InferInfo i = ig.unionDisjoint(n, e);
    i.process(&d_im, true);
    Trace("bags::BagSolver::postCheck") << i << endl;
  }
}

void BagSolver::checkUnionMax(const Node& n)
{
  Assert(n.getKind() == UNION_MAX);
  std::set<Node> elements = getElementsForBinaryOperator(n);
  for (const Node& e : elements)
  {
    InferenceGenerator ig(&d_state);
    InferInfo i = ig.unionMax(n, e);
    i.process(&d_im, true);
    Trace("bags::BagSolver::postCheck") << i << endl;
  }
}

void BagSolver::checkDifferenceSubtract(const Node& n)
{
  Assert(n.getKind() == DIFFERENCE_SUBTRACT);
  std::set<Node> elements = getElementsForBinaryOperator(n);
  for (const Node& e : elements)
  {
    InferenceGenerator ig(&d_state);
    InferInfo i = ig.differenceSubtract(n, e);
    i.process(&d_im, true);
    Trace("bags::BagSolver::postCheck") << i << endl;
  }
}

void BagSolver::checkMkBag(const Node& n)
{
  Assert(n.getKind() == MK_BAG);
  Trace("bags::BagSolver::postCheck")
      << "BagSolver::checkMkBag Elements of " << n
      << " are: " << d_state.getElements(n) << std::endl;
  for (const Node& e : d_state.getElements(n))
  {
    InferenceGenerator ig(&d_state);
    InferInfo i = ig.mkBag(n, e);
    i.process(&d_im, true);
    Trace("bags::BagSolver::postCheck") << i << endl;
  }
}
void BagSolver::checkNonNegativeCountTerms(const Node& bag, const Node& element)
{
  InferenceGenerator ig(&d_state);
  InferInfo i = ig.nonNegativeCount(bag, element);
  i.process(&d_im, true);
  Trace("bags::BagSolver::postCheck") << i << endl;
}

void BagSolver::checkDifferenceRemove(const Node& n)
{
  Assert(n.getKind() == DIFFERENCE_REMOVE);
  std::set<Node> elements = getElementsForBinaryOperator(n);
  for (const Node& e : elements)
  {
    InferenceGenerator ig(&d_state);
    InferInfo i = ig.differenceRemove(n, e);
    i.process(&d_im, true);
    Trace("bags::BagSolver::postCheck") << i << endl;
  }
}

}  // namespace bags
}  // namespace theory
}  // namespace CVC4
