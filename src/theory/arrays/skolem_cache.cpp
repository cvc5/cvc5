/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arrays skolem cache.
 */

#include "theory/arrays/skolem_cache.h"

#include "expr/attribute.h"
#include "expr/bound_var_manager.h"
#include "expr/skolem_manager.h"
#include "expr/type_node.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace arrays {

/**
 * A bound variable corresponding to an index for witnessing the satisfiability
 * of array disequalities.
 */
struct ExtIndexVarAttributeId
{
};
typedef expr::Attribute<ExtIndexVarAttributeId, Node> ExtIndexVarAttribute;

SkolemCache::SkolemCache() {}

Node SkolemCache::getExtIndexSkolem(Node deq)
{
  Assert(deq.getKind() == NOT && deq[0].getKind() == EQUAL);
  Node a = deq[0][0];
  Node b = deq[0][1];
  Assert(a.getType().isArray());
  Assert(b.getType() == a.getType());

  NodeManager* nm = NodeManager::currentNM();

  // get the reference index, which notice is deterministic for a, b in the
  // lifetime of the node manager
  Node x = getExtIndexVar(deq);

  // make the axiom for x
  Node as = nm->mkNode(SELECT, a, x);
  Node bs = nm->mkNode(SELECT, b, x);
  Node deqIndex = as.eqNode(bs).notNode();
  Node axiom = nm->mkNode(IMPLIES, deq, deqIndex);

  // make the skolem that witnesses the above axiom
  SkolemManager* sm = nm->getSkolemManager();
  return sm->mkSkolem(
      x,
      axiom,
      "array_ext_index",
      "an extensional lemma index variable from the theory of arrays");
}

Node SkolemCache::getExtIndexVar(Node deq)
{
  Node a = deq[0][0];
  TypeNode atn = a.getType();
  Assert(atn.isArray());
  Assert(atn == deq[0][1].getType());
  TypeNode atnIndex = atn.getArrayIndexType();
  BoundVarManager* bvm = NodeManager::currentNM()->getBoundVarManager();
  return bvm->mkBoundVar<ExtIndexVarAttribute>(deq, atnIndex);
}

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5
