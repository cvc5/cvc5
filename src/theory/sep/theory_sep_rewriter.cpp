/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Theory of separation logic rewriter.
 */

#include "theory/sep/theory_sep_rewriter.h"

#include "expr/attribute.h"
#include "expr/emptyset.h"
#include "options/sep_options.h"
#include "theory/quantifiers/quant_util.h"

namespace cvc5::internal {
namespace theory {
namespace sep {

TheorySepRewriter::TheorySepRewriter(NodeManager* nm) : TheoryRewriter(nm) {}

void TheorySepRewriter::getStarChildren(Node n,
                                        std::vector<Node>& scs,
                                        std::vector<Node>& nscs) const
{
  Assert(n.getKind() == Kind::SEP_STAR);
  Node tr = nodeManager()->mkConst(true);
  for( unsigned i=0; i<n.getNumChildren(); i++ ){
    if (n[i].getKind() == Kind::SEP_EMP)
    {
      scs.push_back(n[i]);
    }
    else if (n[i].getKind() == Kind::SEP_STAR)
    {
      getStarChildren(n[i], scs, nscs);
    }
    else if (n[i].getKind() == Kind::SEP_PTO)
    {
      scs.push_back(n[i]);
    }
    else
    {
      std::vector<Node> temp_scs;
      getAndChildren(n[i], temp_scs, nscs);
      Node to_add;
      if (temp_scs.size() == 0)
      {
        if (std::find(scs.begin(), scs.end(), tr) == scs.end())
        {
          to_add = tr;
        }
      }
      else if (temp_scs.size() == 1)
      {
        to_add = temp_scs[0];
      }
      else
      {
        to_add = nodeManager()->mkNode(Kind::AND, temp_scs);
      }
      if( !to_add.isNull() ){
        //flatten star
        if (to_add.getKind() == Kind::SEP_STAR)
        {
          getStarChildren(to_add, scs, nscs);
        }
        else if (to_add.getKind() != Kind::SEP_EMP || scs.empty())
        {  // remove sep emp
          scs.push_back(to_add);
        }
      }
    }
  }
}

void TheorySepRewriter::getAndChildren(Node n,
                                       std::vector<Node>& scs,
                                       std::vector<Node>& nscs) const
{
  if (n.getKind() == Kind::AND)
  {
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      getAndChildren(n[i], scs, nscs);
    }
  }
  else
  {
    std::map< Node, bool > visited;
    if( isSpatial( n, visited ) ){
      if (std::find(scs.begin(), scs.end(), n) == scs.end())
      {
        scs.push_back(n);
      }
    }else{
      if (std::find(nscs.begin(), nscs.end(), n) == nscs.end())
      {
        if (n != nodeManager()->mkConst(true))
        {
          nscs.push_back(n);
        }
      }
    }
  }
}

bool TheorySepRewriter::isSpatial(Node n, std::map<Node, bool>& visited) const
{
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    if (n.getKind() == Kind::SEP_STAR || n.getKind() == Kind::SEP_PTO
        || n.getKind() == Kind::SEP_EMP || n.getKind() == Kind::SEP_LABEL)
    {
      return true;
    }
    else if (n.getType().isBoolean())
    {
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        if( isSpatial( n[i], visited ) ){
          return true;
        }
      }
    }
  }
  return false;
}

RewriteResponse TheorySepRewriter::postRewrite(TNode node) {
  Trace("sep-postrewrite") << "Sep::postRewrite start " << node << std::endl;
  Node retNode = node;
  switch (node.getKind()) {
    case Kind::SEP_STAR:
    {
      //flatten
      std::vector<Node> scs;
      std::vector<Node> nscs;
      getStarChildren(node, scs, nscs);
      if (!scs.empty())
      {
        Node schild;
        if (scs.size() == 1)
        {
          schild = scs[0];
        }
        else
        {
          schild = nodeManager()->mkNode(Kind::SEP_STAR, scs);
        }
        nscs.push_back(schild);
      }
      Assert(!nscs.empty());
      if (nscs.size() == 1)
      {
        retNode = nscs[0];
      }
      else
      {
        retNode = nodeManager()->mkNode(Kind::AND, nscs);
      }
      break;
    }
    case Kind::EQUAL:
    {
      if(node[0] == node[1]) {
        return RewriteResponse(REWRITE_DONE, nodeManager()->mkConst(true));
      }
      else if (node[0].isConst() && node[1].isConst()) {
        return RewriteResponse(REWRITE_DONE, nodeManager()->mkConst(false));
      }
      if (node[0] > node[1]) {
        Node newNode = nodeManager()->mkNode(node.getKind(), node[1], node[0]);
        return RewriteResponse(REWRITE_DONE, newNode);
      }
      break;
    }
    default:
      break;
  }
  if( node!=retNode ){
    Trace("sep-rewrite") << "Sep::rewrite : " << node << " -> " << retNode << std::endl;
  }
  return RewriteResponse(node==retNode ? REWRITE_DONE : REWRITE_AGAIN_FULL, retNode);
}

}  // namespace sep
}  // namespace theory
}  // namespace cvc5::internal
