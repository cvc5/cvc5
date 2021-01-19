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
}

struct BagsCountAttributeId
{
};
typedef expr::Attribute<BagsCountAttributeId, Node> BagsCountAttribute;

void SolverState::registerBag(TNode n)
{
  Assert(n.getType().isBag());
  d_bags.insert(n);
}

void SolverState::registerCountTerm(TNode n)
{
  Assert(n.getKind() == BAG_COUNT);
  Node element = n[0];
  Node bag = n[1];
  d_bagElements[bag].insert(element);
}

const std::set<Node>& SolverState::getBags() { return d_bags; }

const std::set<Node>& SolverState::getElements(Node B)
{
  return d_bagElements[B];
}

Node SolverState::getBagSkolem(const Node& bagTerm)
{
  return d_bagSkolems[bagTerm];
}

void SolverState::reset()
{
  d_bagElements.clear();
  d_bags.clear();
}

void SolverState::mergeBags(TNode n1, TNode n2)
{
  // merge the count terms of the two equivalent bags
  const std::set<Node>& terms1 = d_bagElements[n1];
  const std::set<Node>& terms2 = d_bagElements[n2];

  std::set<Node> merge;
  set_union(terms1.begin(),
            terms1.end(),
            terms2.begin(),
            terms2.end(),
            std::inserter(merge, merge.begin()));
  d_bagElements[n1] = merge;
  d_bagElements[n2] = merge;
  Trace("bags::SolverState::mergeBags")
      << "[SolverState::mergeBags] n1: " << n1 << ", count terms1: " << terms1
      << std::endl;
  Trace("bags::SolverState::mergeBags")
      << "[SolverState::mergeBags] n2: " << n2 << ", count terms2: " << terms2
      << std::endl;
  Trace("bags::SolverState::mergeBags")
      << "[SolverState::mergeBags] merge: " << merge << std::endl;
}

}  // namespace bags
}  // namespace theory
}  // namespace CVC4
