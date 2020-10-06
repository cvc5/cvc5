/*********************                                                        */
/*! \file skolem_cache.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Arrays skolem cache
 **/

#include "theory/arrays/skolem_cache.h"

#include "expr/attribute.h"
#include "expr/skolem_manager.h"
#include "expr/type_node.h"

using namespace CVC4::kind;

namespace CVC4 {
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
  ExtIndexVarAttribute eiva;
  if (deq.hasAttribute(eiva))
  {
    return deq.getAttribute(eiva);
  }
  Node a = deq[0][0];
  Node b = deq[0][1];
  TypeNode atn = a.getType();
  Assert(atn.isArray());
  Assert(atn == b.getType());
  TypeNode atnIndex = atn.getArrayIndexType();
  Node v = NodeManager::currentNM()->mkBoundVar(atnIndex);
  deq.setAttribute(eiva, v);
  return v;
}

}  // namespace arrays
}  // namespace theory
}  // namespace CVC4
