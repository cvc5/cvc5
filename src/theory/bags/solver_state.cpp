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
void SolverState::registerClass(TNode n)
{
  TypeNode t = n.getType();
  Kind k = n.getKind();
  if(t.isBag())
  {
    // TODO: check that n is not already there
    d_bags[t].push_back(n);
  }

  if(k == BAG_COUNT)
  {
    // TODO: check that n[0] is not already there
    d_elements[n[0].getType()].push_back(n[0]);
  }
}

std::map<TypeNode, std::vector<Node>> & SolverState::getBags()
{
  return d_bags;
}

std::vector<Node> & SolverState::getBags(TypeNode t)
{
  return d_bags[t];
}

std::vector<Node> & SolverState::getElements(TypeNode t)
{
  return d_elements[t];
}

}  // namespace bags
}  // namespace theory
}  // namespace CVC4
