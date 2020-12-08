/*********************                                                        */
/*! \file term_processor.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of term processor utilities
 **/

#include "proof/term_processor.h"

#include "expr/attribute.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace proof {

TermProcessor::TermProcessor() {}

Node TermProcessor::convert(Node n)
{
  if (n.isNull())
  {
    return n;
  }
  Trace("term-process-debug") << "TermProcessor::convert: " << n << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<Node, Node, NodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = d_cache.find(cur);
    if (it == d_cache.end())
    {
      if (!shouldTraverse(cur))
      {
        d_cache[cur] = cur;
      }
      else
      {
        d_cache[cur] = Node::null();
        visit.push_back(cur);
        if (cur.getMetaKind() == metakind::PARAMETERIZED)
        {
          visit.push_back(cur.getOperator());
        }
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == metakind::PARAMETERIZED)
      {
        it = d_cache.find(cur.getOperator());
        Assert(it != d_cache.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cur.getOperator() != it->second;
        children.push_back(it->second);
      }
      for (const Node& cn : cur)
      {
        it = d_cache.find(cn);
        Assert(it != d_cache.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      // run the callback for the current application
      Node cret = runConvert(ret);
      if (!cret.isNull())
      {
        ret = cret;
      }
      d_cache[cur] = ret;
    }
  } while (!visit.empty());
  Assert(d_cache.find(n) != d_cache.end());
  Assert(!d_cache.find(n)->second.isNull());
  return d_cache[n];
}

TypeNode TermProcessor::convertType(TypeNode tn)
{
  if (tn.isNull())
  {
    return tn;
  }
  Trace("term-process-debug")
      << "TermProcessor::convertType: " << tn << std::endl;
  std::unordered_map<TypeNode, TypeNode, TypeNodeHashFunction>::iterator it;
  std::vector<TypeNode> visit;
  TypeNode cur;
  visit.push_back(tn);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = d_tcache.find(cur);
    if (it == d_tcache.end())
    {
      if (cur.getNumChildren() == 0)
      {
        TypeNode ret = runConvertType(cur);
        d_tcache[cur] = ret;
      }
      else
      {
        d_tcache[cur] = TypeNode::null();
        visit.push_back(cur);
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
    else if (it->second.isNull())
    {
      // reconstruct using a node builder, which seems to be required for
      // type nodes.
      NodeBuilder<> nb(cur.getKind());
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        // push the operator
        nb << cur.getOperator();
      }
      for (TypeNode::const_iterator j = cur.begin(), iend = cur.end();
           j != iend;
           ++j)
      {
        it = d_tcache.find(*j);
        Assert(it != d_tcache.end());
        Assert(!it->second.isNull());
        nb << it->second;
      }
      // construct the type node
      TypeNode ret = nb.constructTypeNode();
      Trace("term-process-debug") << cur << " <- " << ret << std::endl;
      // run the callback for the current application
      TypeNode cret = runConvertType(ret);
      if (!cret.isNull())
      {
        ret = cret;
      }
      Trace("term-process-debug")
          << cur << " <- " << ret << " (post-convert)" << std::endl;
      d_tcache[cur] = ret;
    }
  } while (!visit.empty());
  Assert(d_tcache.find(tn) != d_tcache.end());
  Assert(!d_tcache.find(tn)->second.isNull());
  return d_tcache[tn];
}

Node TermProcessor::runConvert(Node n) { return Node::null(); }

TypeNode TermProcessor::runConvertType(TypeNode tn) { return TypeNode::null(); }
bool TermProcessor::shouldTraverse(Node n) { return true; }

}  // namespace proof
}  // namespace CVC4
