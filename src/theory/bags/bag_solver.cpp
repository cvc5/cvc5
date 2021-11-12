/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Solver for the theory of bags.
 */

#include "theory/bags/bag_solver.h"

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

BagSolver::BagSolver(Env& env,
                     SolverState& s,
                     InferenceManager& im,
                     TermRegistry& tr)
    : EnvObj(env),
      d_state(s),
      d_ig(&s, &im),
      d_im(im),
      d_termReg(tr),
      d_mapCache(userContext())
{
  d_zero = NodeManager::currentNM()->mkConst(CONST_RATIONAL, Rational(0));
  d_one = NodeManager::currentNM()->mkConst(CONST_RATIONAL, Rational(1));
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

BagSolver::~BagSolver() {}

void BagSolver::postCheck()
{
  d_state.initialize();

  checkDisequalBagTerms();

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
        case kind::BAG_EMPTY: checkEmpty(n); break;
        case kind::BAG_MAKE: checkBagMake(n); break;
        case kind::BAG_UNION_DISJOINT: checkUnionDisjoint(n); break;
        case kind::BAG_UNION_MAX: checkUnionMax(n); break;
        case kind::BAG_INTER_MIN: checkIntersectionMin(n); break;
        case kind::BAG_DIFFERENCE_SUBTRACT: checkDifferenceSubtract(n); break;
        case kind::BAG_DIFFERENCE_REMOVE: checkDifferenceRemove(n); break;
        case kind::BAG_DUPLICATE_REMOVAL: checkDuplicateRemoval(n); break;
        case kind::BAG_MAP: checkMap(n); break;
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

void BagSolver::checkEmpty(const Node& n)
{
  Assert(n.getKind() == BAG_EMPTY);
  for (const Node& e : d_state.getElements(n))
  {
    InferInfo i = d_ig.empty(n, e);
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkUnionDisjoint(const Node& n)
{
  Assert(n.getKind() == BAG_UNION_DISJOINT);
  std::set<Node> elements = getElementsForBinaryOperator(n);
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.unionDisjoint(n, e);
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkUnionMax(const Node& n)
{
  Assert(n.getKind() == BAG_UNION_MAX);
  std::set<Node> elements = getElementsForBinaryOperator(n);
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.unionMax(n, e);
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkIntersectionMin(const Node& n)
{
  Assert(n.getKind() == BAG_INTER_MIN);
  std::set<Node> elements = getElementsForBinaryOperator(n);
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.intersection(n, e);
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkDifferenceSubtract(const Node& n)
{
  Assert(n.getKind() == BAG_DIFFERENCE_SUBTRACT);
  std::set<Node> elements = getElementsForBinaryOperator(n);
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.differenceSubtract(n, e);
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkBagMake(const Node& n)
{
  Assert(n.getKind() == BAG_MAKE);
  Trace("bags::BagSolver::postCheck")
      << "BagSolver::checkBagMake Elements of " << n
      << " are: " << d_state.getElements(n) << std::endl;
  for (const Node& e : d_state.getElements(n))
  {
    InferInfo i = d_ig.bagMake(n, e);
    d_im.lemmaTheoryInference(&i);
  }
}
void BagSolver::checkNonNegativeCountTerms(const Node& bag, const Node& element)
{
  InferInfo i = d_ig.nonNegativeCount(bag, element);
  d_im.lemmaTheoryInference(&i);
}

void BagSolver::checkDifferenceRemove(const Node& n)
{
  Assert(n.getKind() == BAG_DIFFERENCE_REMOVE);
  std::set<Node> elements = getElementsForBinaryOperator(n);
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.differenceRemove(n, e);
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkDuplicateRemoval(Node n)
{
  Assert(n.getKind() == BAG_DUPLICATE_REMOVAL);
  set<Node> elements;
  const set<Node>& downwards = d_state.getElements(n);
  const set<Node>& upwards = d_state.getElements(n[0]);

  elements.insert(downwards.begin(), downwards.end());
  elements.insert(upwards.begin(), upwards.end());

  for (const Node& e : elements)
  {
    InferInfo i = d_ig.duplicateRemoval(n, e);
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkDisequalBagTerms()
{
  for (const Node& n : d_state.getDisequalBagTerms())
  {
    InferInfo info = d_ig.bagDisequality(n);
    d_im.lemmaTheoryInference(&info);
  }
}

void BagSolver::checkMap(Node n)
{
  Assert(n.getKind() == BAG_MAP);
  const set<Node>& downwards = d_state.getElements(n);
  const set<Node>& upwards = d_state.getElements(n[1]);
  for (const Node& y : downwards)
  {
    if (d_mapCache.count(n) && d_mapCache[n].get()->contains(y))
    {
      continue;
    }
    auto [downInference, uf, preImageSize] = d_ig.mapDownwards(n, y);
    d_im.lemmaTheoryInference(&downInference);
    for (const Node& x : upwards)
    {
      InferInfo upInference = d_ig.mapUpwards(n, uf, preImageSize, y, x);
      d_im.lemmaTheoryInference(&upInference);
    }
    if (!d_mapCache.count(n))
    {
      std::shared_ptr<context::CDHashSet<Node> > set =
          std::make_shared<context::CDHashSet<Node> >(userContext());
      d_mapCache.insert(n, set);
    }
    d_mapCache[n].get()->insert(y);
  }
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5
