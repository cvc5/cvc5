/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Solver for the theory of bags.
 */

#include "theory/bags/bag_solver.h"

#include "expr/emptybag.h"
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
  d_zero = NodeManager::currentNM()->mkConstInt(Rational(0));
  d_one = NodeManager::currentNM()->mkConstInt(Rational(1));
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

BagSolver::~BagSolver() {}

void BagSolver::checkBasicOperations()
{
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
        case kind::BAG_FILTER: checkFilter(n); break;
        case kind::BAG_MAP: checkMap(n); break;
        case kind::TABLE_PRODUCT: checkProduct(n); break;
        case kind::TABLE_JOIN: checkJoin(n); break;
        case kind::TABLE_GROUP: checkGroup(n); break;
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
      checkNonNegativeCountTerms(n, d_state.getRepresentative(e));
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
    InferInfo i = d_ig.empty(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkUnionDisjoint(const Node& n)
{
  Assert(n.getKind() == BAG_UNION_DISJOINT);
  std::set<Node> elements = getElementsForBinaryOperator(n);
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.unionDisjoint(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkUnionMax(const Node& n)
{
  Assert(n.getKind() == BAG_UNION_MAX);
  std::set<Node> elements = getElementsForBinaryOperator(n);
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.unionMax(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkIntersectionMin(const Node& n)
{
  Assert(n.getKind() == BAG_INTER_MIN);
  std::set<Node> elements = getElementsForBinaryOperator(n);
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.intersection(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkDifferenceSubtract(const Node& n)
{
  Assert(n.getKind() == BAG_DIFFERENCE_SUBTRACT);
  std::set<Node> elements = getElementsForBinaryOperator(n);
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.differenceSubtract(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

bool BagSolver::checkBagMake()
{
  bool sentLemma = false;
  for (const Node& bag : d_state.getBags())
  {
    TypeNode bagType = bag.getType();
    NodeManager* nm = NodeManager::currentNM();
    Node empty = nm->mkConst(EmptyBag(bagType));
    if (d_state.areEqual(empty, bag) || d_state.areDisequal(empty, bag))
    {
      continue;
    }

    // look for BAG_MAKE terms in the equivalent class
    eq::EqClassIterator it =
        eq::EqClassIterator(bag, d_state.getEqualityEngine());
    while (!it.isFinished())
    {
      Node n = (*it);
      if (n.getKind() == BAG_MAKE)
      {
        Trace("bags-check") << "splitting on node " << std::endl;
        InferInfo i = d_ig.bagMake(n);
        sentLemma |= d_im.lemmaTheoryInference(&i);
        // it is enough to split only once per equivalent class
        break;
      }
      it++;
    }
  }
  return sentLemma;
}

void BagSolver::checkBagMake(const Node& n)
{
  Assert(n.getKind() == BAG_MAKE);
  Trace("bags::BagSolver::postCheck")
      << "BagSolver::checkBagMake Elements of " << n
      << " are: " << d_state.getElements(n) << std::endl;
  for (const Node& e : d_state.getElements(n))
  {
    InferInfo i = d_ig.bagMake(n, d_state.getRepresentative(e));
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
    InferInfo i = d_ig.differenceRemove(n, d_state.getRepresentative(e));
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
    InferInfo i = d_ig.duplicateRemoval(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkDisequalBagTerms()
{
  for (const auto& [equality, witness] : d_state.getDisequalBagTerms())
  {
    InferInfo info = d_ig.bagDisequality(equality, witness);
    d_im.lemmaTheoryInference(&info);
  }
}

void BagSolver::checkMap(Node n)
{
  Assert(n.getKind() == BAG_MAP);
  const set<Node>& downwards = d_state.getElements(n);
  const set<Node>& upwards = d_state.getElements(n[1]);
  for (const Node& z : downwards)
  {
    Node y = d_state.getRepresentative(z);
    if (!d_mapCache.count(n))
    {
      std::shared_ptr<context::CDHashMap<Node, std::pair<Node, Node>>> nMap =
          std::make_shared<context::CDHashMap<Node, std::pair<Node, Node>>>(
              userContext());
      d_mapCache[n] = nMap;
    }
    if (!d_mapCache[n].get()->count(y))
    {
      auto [downInference, uf, preImageSize] = d_ig.mapDown(n, y);
      d_im.lemmaTheoryInference(&downInference);
      std::pair<Node, Node> yPair = std::make_pair(uf, preImageSize);
      d_mapCache[n].get()->insert(y, yPair);
    }

    context::CDHashMap<Node, std::pair<Node, Node>>::iterator it =
        d_mapCache[n].get()->find(y);

    auto [uf, preImageSize] = it->second;

    for (const Node& x : upwards)
    {
      InferInfo upInference = d_ig.mapUp(n, uf, preImageSize, y, x);
      d_im.lemmaTheoryInference(&upInference);
    }
  }
}

void BagSolver::checkFilter(Node n)
{
  Assert(n.getKind() == BAG_FILTER);

  set<Node> elements;
  const set<Node>& downwards = d_state.getElements(n);
  const set<Node>& upwards = d_state.getElements(n[1]);
  elements.insert(downwards.begin(), downwards.end());
  elements.insert(upwards.begin(), upwards.end());

  for (const Node& e : elements)
  {
    InferInfo i = d_ig.filterDown(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.filterUp(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkProduct(Node n)
{
  Assert(n.getKind() == TABLE_PRODUCT);
  const set<Node>& elementsA = d_state.getElements(n[0]);
  const set<Node>& elementsB = d_state.getElements(n[1]);

  for (const Node& e1 : elementsA)
  {
    for (const Node& e2 : elementsB)
    {
      InferInfo i = d_ig.productUp(
          n, d_state.getRepresentative(e1), d_state.getRepresentative(e2));
      d_im.lemmaTheoryInference(&i);
    }
  }

  std::set<Node> elements = d_state.getElements(n);
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.productDown(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkJoin(Node n)
{
  Assert(n.getKind() == TABLE_JOIN);
  const set<Node>& elementsA = d_state.getElements(n[0]);
  const set<Node>& elementsB = d_state.getElements(n[1]);

  for (const Node& e1 : elementsA)
  {
    for (const Node& e2 : elementsB)
    {
      InferInfo i = d_ig.joinUp(
          n, d_state.getRepresentative(e1), d_state.getRepresentative(e2));
      d_im.lemmaTheoryInference(&i);
    }
  }

  std::set<Node> elements = d_state.getElements(n);
  for (const Node& e : elements)
  {
    InferInfo i = d_ig.joinDown(n, d_state.getRepresentative(e));
    d_im.lemmaTheoryInference(&i);
  }
}

void BagSolver::checkGroup(Node n)
{
  Assert(n.getKind() == TABLE_GROUP);

  InferInfo notEmpty = d_ig.groupNotEmpty(n);
  d_im.lemmaTheoryInference(&notEmpty);

  Node part = d_ig.defineSkolemPartFunction(n);

  const set<Node>& elementsA = d_state.getElements(n[0]);
  std::shared_ptr<context::CDHashSet<Node>> skolems =
      d_state.getPartElementSkolems(n);
  for (const Node& a : elementsA)
  {
    if (skolems->contains(a))
    {
      // skip skolem elements that were introduced by groupPartCount below.
      continue;
    }
    Node aRep = d_state.getRepresentative(a);
    InferInfo i = d_ig.groupUp1(n, aRep, part);
    d_im.lemmaTheoryInference(&i);
    i = d_ig.groupUp2(n, aRep, part);
    d_im.lemmaTheoryInference(&i);
  }

  std::set<Node> parts = d_state.getElements(n);
  for (std::set<Node>::iterator partIt1 = parts.begin(); partIt1 != parts.end();
       ++partIt1)
  {
    Node part1 = d_state.getRepresentative(*partIt1);
    std::vector<Node> partEqc;
    d_state.getEquivalenceClass(part1, partEqc);
    bool newPart = true;
    for (Node p : partEqc)
    {
      if (p.getKind() == APPLY_UF && p.getOperator() == part)
      {
        newPart = false;
      }
    }
    if (newPart)
    {
      // only apply the groupPartCount rule for a part that does not have
      // nodes of the form (part x) introduced by the group up rule above.
      InferInfo partCardinality = d_ig.groupPartCount(n, part1, part);
      d_im.lemmaTheoryInference(&partCardinality);
    }

    std::set<Node> partElements = d_state.getElements(part1);
    for (std::set<Node>::iterator i = partElements.begin();
         i != partElements.end();
         ++i)
    {
      Node x = d_state.getRepresentative(*i);
      if (!skolems->contains(x))
      {
        // only apply down rules for elements not generated by groupPartCount
        // rule above
        InferInfo down = d_ig.groupDown(n, part1, x, part);
        d_im.lemmaTheoryInference(&down);
      }

      std::set<Node>::iterator j = i;
      ++j;
      while (j != partElements.end())
      {
        Node y = d_state.getRepresentative(*j);
        // x, y should have the same projection
        InferInfo sameProjection =
            d_ig.groupSameProjection(n, part1, x, y, part);
        d_im.lemmaTheoryInference(&sameProjection);
        ++j;
      }

      for (const Node& a : elementsA)
      {
        Node y = d_state.getRepresentative(a);
        if (x != y)
        {
          // x, y should have the same projection
          InferInfo samePart = d_ig.groupSamePart(n, part1, x, y, part);
          d_im.lemmaTheoryInference(&samePart);
        }
      }
    }
  }
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal
