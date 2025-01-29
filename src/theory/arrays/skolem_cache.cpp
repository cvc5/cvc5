/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Andrew Reynolds, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arrays {

/**
 * A bound variable corresponding to the index used in the eqrange expansion.
 */
struct EqRangeVarAttributeId
{
};
typedef expr::Attribute<EqRangeVarAttributeId, Node> EqRangeVarAttribute;

SkolemCache::SkolemCache() {}

Node SkolemCache::getExtIndexSkolem(NodeManager* nm, Node deq)
{
  Assert(deq.getKind() == Kind::NOT && deq[0].getKind() == Kind::EQUAL);
  Node a = deq[0][0];
  Node b = deq[0][1];
  Assert(a.getType().isArray());
  Assert(b.getType() == a.getType());

  // make the skolem, which is deterministic for a,b.
  SkolemManager* sm = nm->getSkolemManager();
  return sm->mkSkolemFunction(SkolemId::ARRAY_DEQ_DIFF, {a, b});
}

Node SkolemCache::getEqRangeVar(NodeManager* nm, TNode eqr)
{
  Assert(eqr.getKind() == Kind::EQ_RANGE);
  BoundVarManager* bvm = nm->getBoundVarManager();
  return bvm->mkBoundVar<EqRangeVarAttribute>(eqr, eqr[2].getType());
}


}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal
