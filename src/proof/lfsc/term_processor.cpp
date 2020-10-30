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

#include "proof/lfsc/term_processor.h"

#include "expr/attribute.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace proof {

Node TermProcessCallback::convert(Node n, bool toInternal)
{
  return toInternal ? convertInternal(n) : convertExternal(n);
}

Node TermProcessCallback::convertInternal(Node n) { return Node::null(); }

Node TermProcessCallback::convertExternal(Node n) { return Node::null(); }

TypeNode TermProcessCallback::convertType(TypeNode tn, bool toInternal)
{
  return toInternal ? convertInternalType(tn) : convertExternalType(tn);
}
TypeNode TermProcessCallback::convertInternalType(TypeNode tn) { return TypeNode::null(); }
TypeNode TermProcessCallback::convertExternalType(TypeNode tn) { return TypeNode::null(); }

TermProcessor::TermProcessor(TermProcessCallback* cb) : d_cb(cb) {}

Node TermProcessor::toInternal(Node n) { return convert(n, true); }
Node TermProcessor::toExternal(Node n) { return convert(n, false); }

Node TermProcessor::convert(Node n, bool toInternal)
{
  if (n.isNull())
  {
    return n;
  }
  Trace("term-process-debug")
      << "TermProcessor::convert: " << toInternal << " " << n << std::endl;
  size_t cachei = toInternal ? 0 : 1;
  std::unordered_map<Node, Node, NodeHashFunction>& cache = d_cache[cachei];
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<Node, Node, NodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = cache.find(cur);
    if (it == cache.end())
    {
      cache[cur] = Node::null();
      visit.push_back(cur);
      if (cur.getMetaKind() == metakind::PARAMETERIZED)
      {
        visit.push_back(cur.getOperator());
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == metakind::PARAMETERIZED)
      {
        it = cache.find(cur.getOperator());
        Assert(it != cache.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cur.getOperator() != it->second;
        children.push_back(it->second);
      }
      for (const Node& cn : cur)
      {
        it = cache.find(cn);
        Assert(it != cache.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      // run the callback for the current application
      ret = d_cb->convert(ret, toInternal);
      cache[cur] = ret;
    }
  } while (!visit.empty());
  Assert(cache.find(n) != cache.end());
  Assert(!cache.find(n)->second.isNull());
  return cache[n];
}

TypeNode TermProcessor::toInternalType(TypeNode tn)
{
  return convertType(tn, true);
}
TypeNode TermProcessor::toExternalType(TypeNode tn)
{
  return convertType(tn, false);
}

TypeNode TermProcessor::convertType(TypeNode tn, bool toInternal)
{
  if (tn.isNull())
  {
    return tn;
  }
  Trace("term-process-debug")
      << "TermProcessor::convertType: " << toInternal << " " << tn << std::endl;
  size_t cachei = toInternal ? 0 : 1;
  std::unordered_map<TypeNode, TypeNode, TypeNodeHashFunction>& cache =
      d_tcache[cachei];
  std::unordered_map<TypeNode, TypeNode, TypeNodeHashFunction>::iterator it;
  std::vector<TypeNode> visit;
  TypeNode cur;
  visit.push_back(tn);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = cache.find(cur);
    if (it == cache.end())
    {
      cache[cur] = TypeNode::null();
      visit.push_back(cur);
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
    else if (it->second.isNull())
    {
      // reconstruct using a node builder
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
        it = cache.find(*j);
        Assert(it != cache.end());
        Assert(!it->second.isNull());
        nb << it->second;
      }
      // construct the type node
      TypeNode ret = nb.constructTypeNode();
      // run the callback for the current application
      ret = d_cb->convertType(ret, toInternal);
      cache[cur] = ret;
    }
  } while (!visit.empty());
  Assert(cache.find(tn) != cache.end());
  Assert(!cache.find(tn)->second.isNull());
  return cache[tn];
}

}  // namespace proof
}  // namespace CVC4
