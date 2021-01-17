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

void SolverState::registerClass(TNode n)
{
  TypeNode t = n.getType();
  if (!t.isBag())
  {
    return;
  }
  d_bags.insert(n);
}

Node SolverState::registerBagElement(TNode n)
{
  Assert(n.getKind() == BAG_COUNT);
  Node element = n[0];
  TypeNode elementType = element.getType();
  Node bag = n[1];
  d_elements[elementType].insert(element);
  NodeManager* nm = NodeManager::currentNM();
  BoundVarManager* bvm = nm->getBoundVarManager();
  Node multiplicity = bvm->mkBoundVar<BagsCountAttribute>(n, nm->integerType());
  Node equal = n.eqNode(multiplicity);
  SkolemManager* sm = nm->getSkolemManager();
  Node skolem = sm->mkSkolem(
      multiplicity,
      equal,
      "bag_multiplicity",
      "an extensional lemma for multiplicity of an element in a bag");
  d_count[bag][element] = skolem;
  Trace("bags::SolverState::registerBagElement")
      << "New skolem: " << skolem << " for " << n << std::endl;

  return skolem;
}

std::set<Node>& SolverState::getBags() { return d_bags; }

std::set<Node>& SolverState::getElements(TypeNode t) { return d_elements[t]; }

std::map<Node, Node>& SolverState::getBagElements(Node B) { return d_count[B]; }

}  // namespace bags
}  // namespace theory
}  // namespace CVC4
