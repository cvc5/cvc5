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
 * Implementation of LFSC node conversion for list variables in side conditions
 */

#include "proof/lfsc/lfsc_list_sc_node_converter.h"

namespace cvc5 {
namespace proof {

LfscListScNodeConverter::LfscListScNodeConverter(
    LfscNodeConverter& conv, const std::unordered_set<Node>& listVars)
    : d_conv(conv), d_listVars(listVars)
{
}

Node LfscListScNodeConverter::postConvert(Node n)
{
  Assert(!NodeManager::isNAryKind(n.getKind()) || n.getNumChildren() == 2);
  // note that after converting to binary form, variables should only appear
  // as the first child of binary applications of n-ary operators
  if (n.getNumChildren() == 2 && d_listVars.find(n[0]) != d_listVars.end())
  {
    // this will fail if e.g. a list variable is a child of a non-n-ary kind
    Assert(NodeManager::isNAryKind(n.getKind()));
    NodeManager* nm = NodeManager::currentNM();
    Kind k = n.getKind();
    TypeNode tn = n.getType();
    // E.g. (or x t) becomes (nary_concat f_or x t false)
    std::vector<Node> children;
    std::vector<TypeNode> childTypes;
    Node f = d_conv.getOperatorOfTerm(n);
    children.push_back(f);
    childTypes.push_back(f.getType());
    for (size_t i = 0; i < 2; i++)
    {
      children.push_back(n[i]);
      childTypes.push_back(n[i].getType());
    }
    Node null = d_conv.getNullTerminator(k, tn);
    AlwaysAssert(!null.isNull())
        << "No null terminator for " << k << ", " << tn;
    children.push_back(null);
    childTypes.push_back(null.getType());
    TypeNode ftype = nm->mkFunctionType(childTypes, tn);
    Node sop = d_conv.mkInternalSymbol("nary_concat", ftype);
    children.insert(children.begin(), sop);
    return nm->mkNode(kind::APPLY_UF, children);
  }
  return n;
}

}  // namespace proof
}  // namespace cvc5
