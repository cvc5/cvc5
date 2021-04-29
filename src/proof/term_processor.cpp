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

using namespace cvc5::kind;

namespace cvc5 {
namespace proof {

NodeConverter::NodeConverter(bool forceIdem) : d_forceIdem(forceIdem) {}

Node NodeConverter::convert(Node n)
{
  if (n.isNull())
  {
    return n;
  }
  Trace("term-process-debug") << "NodeConverter::convert: " << n << std::endl;
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
    Trace("term-process-debug2") << "convert " << cur << std::endl;
    if (it == d_cache.end())
    {
      Assert(d_preCache.find(cur) == d_preCache.end());
      Node curp = preConvert(cur);
      d_preCache[cur] = curp;
      curp = curp.isNull() ? Node(cur) : curp;
      if (!shouldTraverse(curp))
      {
        if (cur != curp)
        {
          addToCache(cur, curp);
        }
        addToCache(curp, curp);
      }
      else
      {
        if (cur != curp)
        {
          d_cache[cur] = Node::null();
          visit.push_back(cur);
        }
        d_cache[curp] = Node::null();
        visit.push_back(curp);
        if (curp.getMetaKind() == metakind::PARAMETERIZED)
        {
          visit.push_back(curp.getOperator());
        }
        visit.insert(visit.end(), curp.begin(), curp.end());
      }
    }
    else if (it->second.isNull())
    {
      it = d_preCache.find(cur);
      Assert(it != d_preCache.end());
      if (!it->second.isNull())
      {
        // it converts to what its prewrite converts to
        Assert(d_cache.find(it->second) != d_cache.end());
        Node ret = d_cache[it->second];
        addToCache(cur, ret);
      }
      else
      {
        Node ret = cur;
        bool childChanged = false;
        std::vector<Node> children;
        if (ret.getMetaKind() == metakind::PARAMETERIZED)
        {
          it = d_cache.find(ret.getOperator());
          Assert(it != d_cache.end());
          Assert(!it->second.isNull());
          childChanged = childChanged || ret.getOperator() != it->second;
          children.push_back(it->second);
        }
        for (const Node& cn : ret)
        {
          it = d_cache.find(cn);
          Assert(it != d_cache.end());
          Assert(!it->second.isNull());
          childChanged = childChanged || cn != it->second;
          children.push_back(it->second);
        }
        if (childChanged)
        {
          ret = nm->mkNode(ret.getKind(), children);
        }
        // run the callback for the current application
        Node cret = postConvert(ret);
        if (!cret.isNull() && ret != cret)
        {
          AlwaysAssert(cret.getType().isComparableTo(ret.getType()))
              << "Converting " << ret << " to " << cret << " changes type";
          ret = cret;
        }
        addToCache(cur, ret);
      }
    }
  } while (!visit.empty());
  Assert(d_cache.find(n) != d_cache.end());
  Assert(!d_cache.find(n)->second.isNull());
  return d_cache[n];
}

TypeNode NodeConverter::convertType(TypeNode tn)
{
  if (tn.isNull())
  {
    return tn;
  }
  Trace("term-process-debug")
      << "NodeConverter::convertType: " << tn << std::endl;
  std::unordered_map<TypeNode, TypeNode, TypeNodeHashFunction>::iterator it;
  std::vector<TypeNode> visit;
  TypeNode cur;
  visit.push_back(tn);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = d_tcache.find(cur);
    Trace("term-process-debug2") << "convert type " << cur << std::endl;
    if (it == d_tcache.end())
    {
      Assert(d_preTCache.find(cur) == d_preTCache.end());
      TypeNode curp = preConvertType(cur);
      d_preTCache[cur] = curp;
      curp = curp.isNull() ? cur : curp;
      if (cur.getNumChildren() == 0)
      {
        TypeNode ret = postConvertType(curp);
        if (cur != curp)
        {
          addToTypeCache(cur, ret);
        }
        addToTypeCache(curp, ret);
      }
      else
      {
        d_tcache[cur] = TypeNode::null();
        visit.push_back(cur);
        visit.push_back(curp);
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
    else if (it->second.isNull())
    {
      it = d_preTCache.find(cur);
      Assert(it != d_preTCache.end());
      if (!it->second.isNull())
      {
        // it converts to what its prewrite converts to
        Assert(d_tcache.find(it->second) != d_cache.end());
        TypeNode ret = d_tcache[it->second];
        addToTypeCache(cur, ret);
      }
      else
      {
        TypeNode ret = cur;
        // reconstruct using a node builder, which seems to be required for
        // type nodes.
        NodeBuilder nb(ret.getKind());
        if (ret.getMetaKind() == kind::metakind::PARAMETERIZED)
        {
          // push the operator
          nb << ret.getOperator();
        }
        for (TypeNode::const_iterator j = ret.begin(), iend = ret.end();
             j != iend;
             ++j)
        {
          it = d_tcache.find(*j);
          Assert(it != d_tcache.end());
          Assert(!it->second.isNull());
          nb << it->second;
        }
        // construct the type node
        ret = nb.constructTypeNode();
        Trace("term-process-debug") << cur << " <- " << ret << std::endl;
        // run the callback for the current application
        TypeNode cret = postConvertType(ret);
        if (!cret.isNull())
        {
          ret = cret;
        }
        Trace("term-process-debug")
            << cur << " <- " << ret << " (post-convert)" << std::endl;
        addToTypeCache(cur, ret);
      }
    }
  } while (!visit.empty());
  Assert(d_tcache.find(tn) != d_tcache.end());
  Assert(!d_tcache.find(tn)->second.isNull());
  Trace("term-process-debug")
      << "NodeConverter::convertType: returns " << d_tcache[tn] << std::endl;
  return d_tcache[tn];
}

void NodeConverter::addToCache(TNode cur, TNode ret)
{
  d_cache[cur] = ret;
  // also force idempotency, if specified
  if (d_forceIdem)
  {
    d_cache[ret] = ret;
  }
}
void NodeConverter::addToTypeCache(TypeNode cur, TypeNode ret)
{
  d_tcache[cur] = ret;
  // also force idempotency, if specified
  if (d_forceIdem)
  {
    d_tcache[ret] = ret;
  }
}

Node NodeConverter::preConvert(Node n) { return Node::null(); }
Node NodeConverter::postConvert(Node n) { return Node::null(); }

TypeNode NodeConverter::preConvertType(TypeNode tn) { return TypeNode::null(); }
TypeNode NodeConverter::postConvertType(TypeNode tn)
{
  return TypeNode::null();
}
bool NodeConverter::shouldTraverse(Node n) { return true; }

}  // namespace proof
}  // namespace cvc5
