/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of LFSC node conversion for list variables in side conditions
 */

#include "proof/lfsc/lfsc_list_sc_node_converter.h"

namespace cvc5::internal {
namespace proof {

LfscListScNodeConverter::LfscListScNodeConverter(
    LfscNodeConverter& conv,
    const std::unordered_set<Node>& listVars,
    bool isPre)
    : d_conv(conv), d_listVars(listVars), d_isPre(isPre)
{
}

Node LfscListScNodeConverter::postConvert(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = n.getKind();
  if (d_isPre)
  {
    // is this an application that may require nary elimination?
    if (NodeManager::isNAryKind(k))
    {
      size_t minLength = 0;
      for (const Node& nc : n)
      {
        if (d_listVars.find(nc) == d_listVars.end())
        {
          minLength++;
          if (minLength >= 2)
          {
            // no need to convert
            return n;
          }
        }
      }
      TypeNode tn = n.getType();
      // if so, (or a b c) becomes (nary_elim f_or (or a b c) false),
      // where the children of this are converted
      std::vector<Node> children;
      Node f = d_conv.getOperatorOfTerm(n);
      children.push_back(f);
      // convert n, since this node will not be converted further
      children.push_back(d_conv.convert(n));
      Node null = d_conv.getNullTerminator(k, tn);
      Assert(!null.isNull());
      // likewise, convert null
      children.push_back(d_conv.convert(null));
      Node sop = mkOperatorFor("nary_elim", children, tn);
      children.insert(children.begin(), sop);
      return nm->mkNode(kind::APPLY_UF, children);
    }
    return n;
  }
  Assert(k == kind::APPLY_UF || k == kind::APPLY_CONSTRUCTOR
         || !NodeManager::isNAryKind(k) || n.getNumChildren() == 2)
      << "Cannot convert LFSC side condition for " << n;
  // note that after converting to binary form, variables should only appear
  // as the first child of binary applications of n-ary operators
  if (n.getNumChildren() == 2 && d_listVars.find(n[0]) != d_listVars.end())
  {
    // this will fail if e.g. a list variable is a child of a non-n-ary kind
    Assert(NodeManager::isNAryKind(k));
    TypeNode tn = n.getType();
    // We are in converted form, but need to get the null terminator for the
    // original term. Hence, we convert the application back to original form
    // if we replaced with an APPLY_UF.
    if (k == kind::APPLY_UF)
    {
      k = d_conv.getBuiltinKindForInternalSymbol(n.getOperator());
      Assert(k != kind::UNDEFINED_KIND);
      // for uniformity, reconstruct in original form
      std::vector<Node> nchildren(n.begin(), n.end());
      n = nm->mkNode(k, nchildren);
    }
    Node null = d_conv.getNullTerminator(k, tn);
    AlwaysAssert(!null.isNull())
        << "No null terminator for " << k << ", " << tn;
    null = d_conv.convert(null);
    // if a list variable occurs as a rightmost child, then we return just
    // the variable
    if (n[1] == null)
    {
      return n[0];
    }
    // E.g. (or x t) becomes (nary_concat f_or x t false)
    std::vector<Node> children;
    Node f = d_conv.getOperatorOfTerm(n);
    children.push_back(f);
    children.insert(children.end(), n.begin(), n.end());
    children.push_back(null);
    Node sop = mkOperatorFor("nary_concat", children, tn);
    children.insert(children.begin(), sop);
    return nm->mkNode(kind::APPLY_UF, children);
  }
  return n;
}

Node LfscListScNodeConverter::mkOperatorFor(const std::string& name,
                                            const std::vector<Node>& children,
                                            TypeNode retType)
{
  NodeManager* nm = NodeManager::currentNM();
  std::vector<TypeNode> childTypes;
  for (const Node& c : children)
  {
    childTypes.push_back(c.getType());
  }
  TypeNode ftype = nm->mkFunctionType(childTypes, retType);
  return d_conv.mkInternalSymbol(name, ftype);
}

}  // namespace proof
}  // namespace cvc5::internal
