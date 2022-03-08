/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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
#include "theory/uf/equality_engine.h"

using namespace std;
using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace bags {

SolverState::SolverState(Env& env, Valuation val) : TheoryState(env, val)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  d_nm = NodeManager::currentNM();
}

void SolverState::registerBag(TNode n)
{
  Assert(n.getType().isBag());
  d_bags.insert(n);
  if (!d_ee->hasTerm(n))
  {
    d_ee->addTerm(n);
  }
}

Node SolverState::registerCountTerm(TNode n)
{
  Assert(n.getKind() == BAG_COUNT);
  Node element = getRepresentative(n[0]);
  Node bag = getRepresentative(n[1]);
  Node count = d_nm->mkNode(BAG_COUNT, element, bag);
  Node skolem = d_nm->getSkolemManager()->mkPurifySkolem(count, "bag.count");
  std::pair<Node, Node> pair = std::make_pair(element, skolem);
  if (std::find(d_bagElements[bag].begin(), d_bagElements[bag].end(), pair)
      == d_bagElements[bag].end())
  {
    d_bagElements[bag].push_back(pair);
  }
  return count.eqNode(skolem);
}

Node SolverState::registerCardinalityTerm(TNode n)
{
  Assert(n.getKind() == BAG_CARD);
  if (!d_ee->hasTerm(n))
  {
    d_ee->addTerm(n);
  }
  Node bag = getRepresentative(n[0]);
  Node cardTerm = d_nm->mkNode(BAG_CARD, bag);
  Node skolem = d_nm->getSkolemManager()->mkPurifySkolem(cardTerm, "bag.card");
  d_cardTerms[cardTerm] = skolem;
  return cardTerm.eqNode(skolem).andNode(skolem.eqNode(n));
}

Node SolverState::getCardinalitySkolem(TNode n)
{
  Assert(n.getKind() == BAG_CARD);
  Node bag = getRepresentative(n[0]);
  Node cardTerm = d_nm->mkNode(BAG_CARD, bag);
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

const std::set<Node>& SolverState::getDisequalBagTerms() { return d_deq; }

void SolverState::reset()
{
  d_bagElements.clear();
  d_bags.clear();
  d_deq.clear();
  d_cardTerms.clear();
}

std::vector<Node> SolverState::initialize()
{
  reset();
  collectDisequalBagTerms();
  return collectBagsAndCountTerms();
}

std::vector<Node> SolverState::collectBagsAndCountTerms()
{
  std::vector<Node> lemmas;

  eq::EqClassesIterator repIt = eq::EqClassesIterator(d_ee);
  while (!repIt.isFinished())
  {
    Node eqc = (*repIt);
    Trace("bags-eqc") << "(eqc " << eqc << std::endl << "";

    if (eqc.getType().isBag())
    {
      registerBag(eqc);
    }

    eq::EqClassIterator it = eq::EqClassIterator(eqc, d_ee);
    while (!it.isFinished())
    {
      Node n = (*it);
      Trace("bags-eqc") << (*it) << " ";
      Kind k = n.getKind();
      if (k == BAG_MAKE)
      {
        // for terms (bag x c) we need to store x by registering the count term
        // (bag.count x (bag x c))
        Node count = d_nm->mkNode(BAG_COUNT, n[0], n);
        Node lemma = registerCountTerm(count);
        lemmas.push_back(lemma);
        Trace("SolverState::collectBagsAndCountTerms")
            << "registered " << count << endl;
      }
      if (k == BAG_COUNT)
      {
        // this takes care of all count terms in each equivalent class
        Node lemma = registerCountTerm(n);
        lemmas.push_back(lemma);
        Trace("SolverState::collectBagsAndCountTerms")
            << "registered " << n << endl;
      }
      if (k == BAG_CARD)
      {
        Node lemma = registerCardinalityTerm(n);
        lemmas.push_back(lemma);
      }
      ++it;
    }
    Trace("bags-eqc") << std::endl << " ) " << std::endl;
    ++repIt;
  }

  Trace("bags-eqc") << "(bagRepresentatives " << d_bags << ")" << std::endl;
  return lemmas;
}

void SolverState::collectDisequalBagTerms()
{
  eq::EqClassIterator it = eq::EqClassIterator(d_false, d_ee);
  while (!it.isFinished())
  {
    Node n = (*it);
    if (n.getKind() == EQUAL && n[0].getType().isBag())
    {
      Trace("bags-eqc") << "(disequalTerms " << n << " )" << std::endl;
      d_deq.insert(n);
    }
    ++it;
  }
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5
