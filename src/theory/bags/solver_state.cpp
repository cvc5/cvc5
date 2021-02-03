/*********************                                                        */
/*! \file solver_state.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed, Morgan Deters, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of bags state object
 **/

#include "theory/bags/solver_state.h"

#include "expr/attribute.h"
#include "expr/bound_var_manager.h"
#include "expr/skolem_manager.h"
#include "theory/uf/equality_engine.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace bags {

SolverState::SolverState(context::Context* c,
                         context::UserContext* u,
                         Valuation val)
    : TheoryState(c, u, val)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  d_nm = NodeManager::currentNM();
}

void SolverState::registerBag(TNode n)
{
  Assert(n.getType().isBag());
  d_bags.insert(n);
}

void SolverState::registerCountTerm(TNode n)
{
  Assert(n.getKind() == BAG_COUNT);
  Node element = getRepresentative(n[0]);
  Node bag = getRepresentative(n[1]);
  d_bagElements[bag].insert(element);
}

const std::set<Node>& SolverState::getBags() { return d_bags; }

const std::set<Node>& SolverState::getElements(Node B)
{
  Node bag = getRepresentative(B);
  return d_bagElements[bag];
}

const std::set<Node>& SolverState::getDisequalBagTerms() { return d_deq; }

void SolverState::reset()
{
  d_bagElements.clear();
  d_bags.clear();
  d_deq.clear();
}

void SolverState::initialize()
{
  reset();
  collectBagsAndCountTerms();
  collectDisequalBagTerms();
}

void SolverState::collectBagsAndCountTerms()
{
  eq::EqClassesIterator repIt = eq::EqClassesIterator(d_ee);
  while (!repIt.isFinished())
  {
    Node eqc = (*repIt);
    Trace("bags-eqc") << "Eqc [ " << eqc << " ] = { ";

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
      if (k == MK_BAG)
      {
        // for terms (bag x c) we need to store x by registering the count term
        // (bag.count x (bag x c))
        Node count = d_nm->mkNode(BAG_COUNT, n[0], n);
        registerCountTerm(count);
        Trace("SolverState::collectBagsAndCountTerms")
            << "registered " << count << endl;
      }
      if (k == BAG_COUNT)
      {
        // this takes care of all count terms in each equivalent class
        registerCountTerm(n);
        Trace("SolverState::collectBagsAndCountTerms")
            << "registered " << n << endl;
      }
      ++it;
    }
    Trace("bags-eqc") << " } " << std::endl;
    ++repIt;
  }

  Trace("bags-eqc") << "bag representatives: " << d_bags << endl;
  Trace("bags-eqc") << "bag elements: " << d_bagElements << endl;
}

void SolverState::collectDisequalBagTerms()
{
  eq::EqClassIterator it = eq::EqClassIterator(d_false, d_ee);
  while (!it.isFinished())
  {
    Node n = (*it);
    if (n.getKind() == EQUAL && n[0].getType().isBag())
    {
      Trace("bags-eqc") << "Disequal terms: " << n << std::endl;
      d_deq.insert(n);
    }
    ++it;
  }
}

}  // namespace bags
}  // namespace theory
}  // namespace CVC4
