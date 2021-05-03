/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Expand definitions for floating-point arithmetic.
 */

#include "theory/fp/fp_expand_defs.h"

#include "expr/skolem_manager.h"

namespace cvc5 {
namespace theory {
namespace fp {

namespace removeToFPGeneric {

Node removeToFPGeneric(TNode node)
{
  Assert(node.getKind() == kind::FLOATINGPOINT_TO_FP_GENERIC);

  FloatingPointToFPGeneric info =
      node.getOperator().getConst<FloatingPointToFPGeneric>();

  size_t children = node.getNumChildren();

  Node op;
  NodeManager* nm = NodeManager::currentNM();

  if (children == 1)
  {
    op = nm->mkConst(FloatingPointToFPIEEEBitVector(info));
    return nm->mkNode(op, node[0]);
  }
  else
  {
    Assert(children == 2);
    Assert(node[0].getType().isRoundingMode());

    TypeNode t = node[1].getType();

    if (t.isFloatingPoint())
    {
      op = nm->mkConst(FloatingPointToFPFloatingPoint(info));
    }
    else if (t.isReal())
    {
      op = nm->mkConst(FloatingPointToFPReal(info));
    }
    else if (t.isBitVector())
    {
      op = nm->mkConst(FloatingPointToFPSignedBitVector(info));
    }
    else
    {
      throw TypeCheckingExceptionPrivate(
          node,
          "cannot rewrite to_fp generic due to incorrect type of second "
          "argument");
    }

    return nm->mkNode(op, node[0], node[1]);
  }

  Unreachable() << "to_fp generic not rewritten";
}
}  // namespace removeToFPGeneric

FpExpandDefs::FpExpandDefs(context::UserContext* u)
    :

      d_minMap(u),
      d_maxMap(u),
      d_toUBVMap(u),
      d_toSBVMap(u),
      d_toRealMap(u)
{
}

Node FpExpandDefs::minUF(Node node)
{
  Assert(node.getKind() == kind::FLOATINGPOINT_MIN);
  TypeNode t(node.getType());
  Assert(t.getKind() == kind::FLOATINGPOINT_TYPE);

  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  ComparisonUFMap::const_iterator i(d_minMap.find(t));

  Node fun;
  if (i == d_minMap.end())
  {
    std::vector<TypeNode> args(2);
    args[0] = t;
    args[1] = t;
    fun = sm->mkDummySkolem("floatingpoint_min_zero_case",
                            nm->mkFunctionType(args,
#ifdef SYMFPUPROPISBOOL
                                               nm->booleanType()
#else
                                               nm->mkBitVectorType(1U)
#endif
                                                   ),
                            "floatingpoint_min_zero_case",
                            NodeManager::SKOLEM_EXACT_NAME);
    d_minMap.insert(t, fun);
  }
  else
  {
    fun = (*i).second;
  }
  return nm->mkNode(kind::APPLY_UF,
                    fun,
                    node[1],
                    node[0]);  // Application reverses the order or arguments
}

Node FpExpandDefs::maxUF(Node node)
{
  Assert(node.getKind() == kind::FLOATINGPOINT_MAX);
  TypeNode t(node.getType());
  Assert(t.getKind() == kind::FLOATINGPOINT_TYPE);

  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  ComparisonUFMap::const_iterator i(d_maxMap.find(t));

  Node fun;
  if (i == d_maxMap.end())
  {
    std::vector<TypeNode> args(2);
    args[0] = t;
    args[1] = t;
    fun = sm->mkDummySkolem("floatingpoint_max_zero_case",
                            nm->mkFunctionType(args,
#ifdef SYMFPUPROPISBOOL
                                               nm->booleanType()
#else
                                               nm->mkBitVectorType(1U)
#endif
                                                   ),
                            "floatingpoint_max_zero_case",
                            NodeManager::SKOLEM_EXACT_NAME);
    d_maxMap.insert(t, fun);
  }
  else
  {
    fun = (*i).second;
  }
  return nm->mkNode(kind::APPLY_UF, fun, node[1], node[0]);
}

Node FpExpandDefs::toUBVUF(Node node)
{
  Assert(node.getKind() == kind::FLOATINGPOINT_TO_UBV);

  TypeNode target(node.getType());
  Assert(target.getKind() == kind::BITVECTOR_TYPE);

  TypeNode source(node[1].getType());
  Assert(source.getKind() == kind::FLOATINGPOINT_TYPE);

  std::pair<TypeNode, TypeNode> p(source, target);
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  ConversionUFMap::const_iterator i(d_toUBVMap.find(p));

  Node fun;
  if (i == d_toUBVMap.end())
  {
    std::vector<TypeNode> args(2);
    args[0] = nm->roundingModeType();
    args[1] = source;
    fun = sm->mkDummySkolem("floatingpoint_to_ubv_out_of_range_case",
                            nm->mkFunctionType(args, target),
                            "floatingpoint_to_ubv_out_of_range_case",
                            NodeManager::SKOLEM_EXACT_NAME);
    d_toUBVMap.insert(p, fun);
  }
  else
  {
    fun = (*i).second;
  }
  return nm->mkNode(kind::APPLY_UF, fun, node[0], node[1]);
}

Node FpExpandDefs::toSBVUF(Node node)
{
  Assert(node.getKind() == kind::FLOATINGPOINT_TO_SBV);

  TypeNode target(node.getType());
  Assert(target.getKind() == kind::BITVECTOR_TYPE);

  TypeNode source(node[1].getType());
  Assert(source.getKind() == kind::FLOATINGPOINT_TYPE);

  std::pair<TypeNode, TypeNode> p(source, target);
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  ConversionUFMap::const_iterator i(d_toSBVMap.find(p));

  Node fun;
  if (i == d_toSBVMap.end())
  {
    std::vector<TypeNode> args(2);
    args[0] = nm->roundingModeType();
    args[1] = source;
    fun = sm->mkDummySkolem("floatingpoint_to_sbv_out_of_range_case",
                            nm->mkFunctionType(args, target),
                            "floatingpoint_to_sbv_out_of_range_case",
                            NodeManager::SKOLEM_EXACT_NAME);
    d_toSBVMap.insert(p, fun);
  }
  else
  {
    fun = (*i).second;
  }
  return nm->mkNode(kind::APPLY_UF, fun, node[0], node[1]);
}

Node FpExpandDefs::toRealUF(Node node)
{
  Assert(node.getKind() == kind::FLOATINGPOINT_TO_REAL);
  TypeNode t(node[0].getType());
  Assert(t.getKind() == kind::FLOATINGPOINT_TYPE);

  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  ComparisonUFMap::const_iterator i(d_toRealMap.find(t));

  Node fun;
  if (i == d_toRealMap.end())
  {
    std::vector<TypeNode> args(1);
    args[0] = t;
    fun = sm->mkDummySkolem("floatingpoint_to_real_infinity_and_NaN_case",
                            nm->mkFunctionType(args, nm->realType()),
                            "floatingpoint_to_real_infinity_and_NaN_case",
                            NodeManager::SKOLEM_EXACT_NAME);
    d_toRealMap.insert(t, fun);
  }
  else
  {
    fun = (*i).second;
  }
  return nm->mkNode(kind::APPLY_UF, fun, node[0]);
}

TrustNode FpExpandDefs::expandDefinition(Node node)
{
  Trace("fp-expandDefinition")
      << "FpExpandDefs::expandDefinition(): " << node << std::endl;

  Node res = node;
  Kind kind = node.getKind();

  if (kind == kind::FLOATINGPOINT_TO_FP_GENERIC)
  {
    res = removeToFPGeneric::removeToFPGeneric(node);
  }
  else if (kind == kind::FLOATINGPOINT_MIN)
  {
    res = NodeManager::currentNM()->mkNode(
        kind::FLOATINGPOINT_MIN_TOTAL, node[0], node[1], minUF(node));
  }
  else if (kind == kind::FLOATINGPOINT_MAX)
  {
    res = NodeManager::currentNM()->mkNode(
        kind::FLOATINGPOINT_MAX_TOTAL, node[0], node[1], maxUF(node));
  }
  else if (kind == kind::FLOATINGPOINT_TO_UBV)
  {
    FloatingPointToUBV info = node.getOperator().getConst<FloatingPointToUBV>();
    FloatingPointToUBVTotal newInfo(info);

    res =
        NodeManager::currentNM()->mkNode(  // kind::FLOATINGPOINT_TO_UBV_TOTAL,
            NodeManager::currentNM()->mkConst(newInfo),
            node[0],
            node[1],
            toUBVUF(node));
  }
  else if (kind == kind::FLOATINGPOINT_TO_SBV)
  {
    FloatingPointToSBV info = node.getOperator().getConst<FloatingPointToSBV>();
    FloatingPointToSBVTotal newInfo(info);

    res =
        NodeManager::currentNM()->mkNode(  // kind::FLOATINGPOINT_TO_SBV_TOTAL,
            NodeManager::currentNM()->mkConst(newInfo),
            node[0],
            node[1],
            toSBVUF(node));
  }
  else if (kind == kind::FLOATINGPOINT_TO_REAL)
  {
    res = NodeManager::currentNM()->mkNode(
        kind::FLOATINGPOINT_TO_REAL_TOTAL, node[0], toRealUF(node));
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
}  // namespace cvc5
