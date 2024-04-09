/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Martin Brain, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Expand definitions for floating-point arithmetic.
 */

#include "theory/fp/fp_expand_defs.h"

#include "expr/skolem_manager.h"
#include "expr/sort_to_term.h"
#include "util/floatingpoint.h"

namespace cvc5::internal {
namespace theory {
namespace fp {

Node FpExpandDefs::minMaxUF(TNode node)
{
  Kind kind = node.getKind();
  Assert(kind == Kind::FLOATINGPOINT_MIN || kind == Kind::FLOATINGPOINT_MAX);

  TypeNode type = node.getType();
  Assert(type.getKind() == Kind::FLOATINGPOINT_TYPE);

  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(Kind::APPLY_UF,
                    nm->getSkolemManager()->mkSkolemFunction(
                        kind == Kind::FLOATINGPOINT_MIN
                                || kind == Kind::FLOATINGPOINT_MIN_TOTAL
                            ? SkolemId::FP_MIN_ZERO
                            : SkolemId::FP_MAX_ZERO,
                        {nm->mkConst(SortToTerm(type))}),
                    node[0],
                    node[1]);
}

Node FpExpandDefs::toUbvSbvUF(TNode node)
{
  Kind kind = node.getKind();
  Assert(kind == Kind::FLOATINGPOINT_TO_UBV
         || kind == Kind::FLOATINGPOINT_TO_SBV);

  TypeNode type = node.getType();
  Assert(type.getKind() == Kind::BITVECTOR_TYPE);

  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(
      Kind::APPLY_UF,
      nm->getSkolemManager()->mkSkolemFunction(
          kind == Kind::FLOATINGPOINT_TO_SBV ? SkolemId::FP_TO_SBV
                                             : SkolemId::FP_TO_UBV,
          {nm->mkConst(SortToTerm(node[1].getType())),
           nm->mkConst(SortToTerm(type))}),
      node[0],
      node[1]);
}

Node FpExpandDefs::toRealUF(TNode node)
{
  Assert(node.getKind() == Kind::FLOATINGPOINT_TO_REAL);
  TypeNode type = node[0].getType();
  Assert(type.getKind() == Kind::FLOATINGPOINT_TYPE);

  NodeManager* nm = NodeManager::currentNM();

  return nm->mkNode(Kind::APPLY_UF,
                    nm->getSkolemManager()->mkSkolemFunction(
                        SkolemId::FP_TO_REAL, {nm->mkConst(SortToTerm(type))}),
                    node[0]);
}

TrustNode FpExpandDefs::expandDefinition(Node node)
{
  Trace("fp-expandDefinition")
      << "FpExpandDefs::expandDefinition(): " << node << std::endl;

  Node res = node;
  Kind kind = node.getKind();
  NodeManager* nm = NodeManager::currentNM();

  if (kind == Kind::FLOATINGPOINT_MIN)
  {
    res = nm->mkNode(
        Kind::FLOATINGPOINT_MIN_TOTAL, node[0], node[1], minMaxUF(node));
  }
  else if (kind == Kind::FLOATINGPOINT_MAX)
  {
    res = nm->mkNode(
        Kind::FLOATINGPOINT_MAX_TOTAL, node[0], node[1], minMaxUF(node));
  }
  else if (kind == Kind::FLOATINGPOINT_TO_UBV)
  {
    res = nm->mkNode(  // Kind::FLOATINGPOINT_TO_UBV_TOTAL,
        nm->mkConst(FloatingPointToUBVTotal(
            node.getOperator().getConst<FloatingPointToUBV>())),
        node[0],
        node[1],
        toUbvSbvUF(node));
  }
  else if (kind == Kind::FLOATINGPOINT_TO_SBV)
  {
    res = nm->mkNode(  // Kind::FLOATINGPOINT_TO_SBV_TOTAL,
        nm->mkConst(FloatingPointToSBVTotal(
            node.getOperator().getConst<FloatingPointToSBV>())),
        node[0],
        node[1],
        toUbvSbvUF(node));
  }
  else if (kind == Kind::FLOATINGPOINT_TO_REAL)
  {
    res =
        nm->mkNode(Kind::FLOATINGPOINT_TO_REAL_TOTAL, node[0], toRealUF(node));
  }

  if (res != node)
  {
    Trace("fp-expandDefinition") << "FpExpandDefs::expandDefinition(): " << node
                                 << " rewritten to " << res << std::endl;
    return TrustNode::mkTrustRewrite(node, res, nullptr);
  }
  return TrustNode::null();
}

}  // namespace fp
}  // namespace theory
}  // namespace cvc5::internal
