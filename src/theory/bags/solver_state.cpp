/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of bags state object.
 */

#include "theory/bags/solver_state.h"

#include "expr/attribute.h"
#include "expr/bound_var_manager.h"
#include "expr/skolem_manager.h"
#include "theory/smt_engine_subsolver.h"
#include "theory/uf/equality_engine.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace bags {

SolverState::SolverState(Env& env, Valuation val)
    : TheoryState(env, val), d_partElementSkolems(env.getUserContext())
{
  d_true = nodeManager()->mkConst(true);
  d_false = nodeManager()->mkConst(false);
  d_nm = nodeManager();
}

void SolverState::registerBag(TNode n)
{
  Assert(n.getType().isBag());
  d_bags.insert(n);
}

void SolverState::registerCountTerm(Node bag, Node element, Node skolem)
{
  Assert(bag.getType().isBag() && bag == getRepresentative(bag));
  Assert(element.getType() == bag.getType().getBagElementType()
         && element == getRepresentative(element));
  Assert(skolem.isVar() && skolem.getType().isInteger());
  std::pair<Node, Node> pair = std::make_pair(element, skolem);
  if (std::find(d_bagElements[bag].begin(), d_bagElements[bag].end(), pair)
      == d_bagElements[bag].end())
  {
    d_bagElements[bag].push_back(pair);
  }
}

void SolverState::registerGroupTerm(Node n)
{
  std::shared_ptr<context::CDHashSet<Node>> set =
      std::make_shared<context::CDHashSet<Node>>(d_env.getUserContext());
  d_partElementSkolems[n] = set;
}

void SolverState::registerCardinalityTerm(Node n, Node skolem)
{
  Assert(n.getKind() == Kind::BAG_CARD);
  Assert(skolem.isVar());
  d_cardTerms[n] = skolem;
}

Node SolverState::getCardinalitySkolem(Node n)
{
  Assert(n.getKind() == Kind::BAG_CARD);
  Node bag = getRepresentative(n[0]);
  Node cardTerm = d_nm->mkNode(Kind::BAG_CARD, bag);
  return d_cardTerms[cardTerm];
}

bool SolverState::hasCardinalityTerms() const { return !d_cardTerms.empty(); }

const std::set<Node>& SolverState::getBags() { return d_bags; }

const std::map<Node, Node>& SolverState::getCardinalityTerms()
{
  return d_cardTerms;
}

std::set<Node> SolverState::getElements(Node B)
{
  Node bag = getRepresentative(B);
  std::set<Node> elements;
  std::vector<std::pair<Node, Node>> pairs = d_bagElements[bag];
  for (std::pair<Node, Node> pair : pairs)
  {
    elements.insert(pair.first);
  }
  return elements;
}

const std::vector<std::pair<Node, Node>>& SolverState::getElementCountPairs(
    Node n)
{
  Node bag = getRepresentative(n);
  return d_bagElements[bag];
}

struct BagsDeqAttributeId
{
};
typedef expr::Attribute<BagsDeqAttributeId, Node> BagsDeqAttribute;

void SolverState::collectDisequalBagTerms()
{
  eq::EqClassIterator it = eq::EqClassIterator(d_false, d_ee);
  while (!it.isFinished())
  {
    Node n = (*it);
    if (n.getKind() == Kind::EQUAL && n[0].getType().isBag())
    {
      Trace("bags-eqc") << "Disequal terms: " << n << std::endl;
      Node A = getRepresentative(n[0]);
      Node B = getRepresentative(n[1]);
      Node equal = A <= B ? A.eqNode(B) : B.eqNode(A);
      if (d_deq.find(equal) == d_deq.end())
      {
        SkolemManager* sm = d_nm->getSkolemManager();
        Node skolem = sm->mkSkolemFunction(SkolemId::BAGS_DEQ_DIFF, {A, B});
        d_deq[equal] = skolem;
      }
    }
    ++it;
  }
}

const std::map<Node, Node>& SolverState::getDisequalBagTerms() { return d_deq; }

void SolverState::registerPartElementSkolem(Node group, Node skolemElement)
{
  Assert(group.getKind() == Kind::TABLE_GROUP);
  Assert(skolemElement.getType() == group[0].getType().getBagElementType());
  d_partElementSkolems[group].get()->insert(skolemElement);
}

std::shared_ptr<context::CDHashSet<Node>> SolverState::getPartElementSkolems(
    Node n)
{
  Assert(n.getKind() == Kind::TABLE_GROUP);
  return d_partElementSkolems[n];
}

void SolverState::reset()
{
  d_bagElements.clear();
  d_bags.clear();
  d_deq.clear();
  d_cardTerms.clear();
}

void SolverState::checkInjectivity(Node n)
{
  SkolemManager* sm = d_nm->getSkolemManager();
  Node f = sm->getOriginalForm(n);
  if (d_functions.find(f) != d_functions.end())
  {
    // we already know f
    return;
  }

  if (f.isVar())
  {
    // no need to solve. f can be assigned any non injective function
    d_functions[f] = false;
    return;
  }

  TypeNode domainType = f.getType().getArgTypes()[0];
  Node x = NodeManager::mkDummySkolem("x", domainType);
  Node y = NodeManager::mkDummySkolem("y", domainType);
  Node f_x = d_nm->mkNode(Kind::APPLY_UF, f, x);
  Node f_y = d_nm->mkNode(Kind::APPLY_UF, f, y);
  Node f_x_equals_f_y = f_x.eqNode(f_y);
  Node not_x_equals_y = x.eqNode(y).notNode();
  Node query = f_x_equals_f_y.andNode(not_x_equals_y);

  Options subOptions;
  subOptions.copyValues(d_env.getOptions());
  SubsolverSetupInfo ssi(d_env, subOptions);
  Result result = checkWithSubsolver(query, ssi);
  if (result.getStatus() == Result::Status::UNSAT)
  {
    d_functions[f] = true;
  }
  else
  {
    d_functions[f] = false;
  }
}

bool SolverState::isInjective(Node n) const
{
  Node f = d_nm->getSkolemManager()->getOriginalForm(n);
  if (d_functions.find(f) != d_functions.end())
  {
    return d_functions.at(f);
  }
  return false;
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal
