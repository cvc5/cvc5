/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Node converter utility
 */

#include "expr/node_converter.h"

#include "expr/attribute.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

NodeConverter::NodeConverter(bool forceIdem) : d_forceIdem(forceIdem) {}

Node NodeConverter::convert(Node n, bool preserveTypes)
{
  if (n.isNull())
  {
    return n;
  }
  Trace("nconv-debug") << "NodeConverter::convert: " << n << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<Node, Node>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = d_cache.find(cur);
    Trace("nconv-debug2") << "convert " << cur << std::endl;
    if (it == d_cache.end())
    {
      d_cache[cur] = Node::null();
      Assert(d_preCache.find(cur) == d_preCache.end());
      Node curp = preConvert(cur);
      // If curp = cur, then we did not pre-rewrite. Hence, we should not
      // revisit cur, and instead set curp to null.
      curp = curp == cur ? Node::null() : curp;
      d_preCache[cur] = curp;
      if (!curp.isNull())
      {
        Trace("nconv-debug2")
            << "..pre-rewrite changed " << cur << " into " << curp << std::endl;
        AlwaysAssert(!preserveTypes
                     || cur.getType().isComparableTo(curp.getType()))
            << "Pre-converting " << cur << " to " << curp << " changes type";
        visit.push_back(cur);
        visit.push_back(curp);
      }
      else
      {
        if (!shouldTraverse(cur))
        {
          addToCache(cur, cur);
        }
        else
        {
          visit.push_back(cur);
          if (cur.getMetaKind() == metakind::PARAMETERIZED)
          {
            visit.push_back(cur.getOperator());
          }
          visit.insert(visit.end(), cur.begin(), cur.end());
        }
      }
    }
    else if (it->second.isNull())
    {
      Trace("nconv-debug2") << "..post-visit " << cur << std::endl;
      it = d_preCache.find(cur);
      Assert(it != d_preCache.end());
      if (!it->second.isNull())
      {
        // it converts to what its prewrite converts to
        Assert(d_cache.find(it->second) != d_cache.end());
        Node ret = d_cache[it->second];
        addToCache(cur, ret);
        Trace("nconv-debug2")
            << "..from cache changed " << cur << " into " << ret << std::endl;
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
        if (preserveTypes)
        {
          if (childChanged)
          {
            ret = nm->mkNode(ret.getKind(), children);
            Trace("nconv-debug2") << "..from children changed " << cur
                                  << " into " << ret << std::endl;
          }
          // run the callback for the current application
          Node cret = postConvert(ret);
          if (!cret.isNull() && ret != cret)
          {
            AlwaysAssert(cret.getType().isComparableTo(ret.getType()))
                << "Converting " << ret << " to " << cret << " changes type";
            Trace("nconv-debug2") << "..post-rewrite changed " << ret
                                  << " into " << cret << std::endl;
            ret = cret;
          }
        }
        else
        {
          // use the untyped version
          Node cret = postConvertUntyped(cur, children, childChanged);
          if (!cret.isNull())
          {
            ret = cret;
          }
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
  Trace("nconv-debug") << "NodeConverter::convertType: " << tn << std::endl;
  std::unordered_map<TypeNode, TypeNode>::iterator it;
  std::vector<TypeNode> visit;
  TypeNode cur;
  visit.push_back(tn);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = d_tcache.find(cur);
    Trace("nconv-debug2") << "convert type " << cur << std::endl;
    if (it == d_tcache.end())
    {
      d_tcache[cur] = TypeNode::null();
      Assert(d_preTCache.find(cur) == d_preTCache.end());
      TypeNode curp = preConvertType(cur);
      // if curp = cur, set null to avoid infinite loop
      curp = curp == cur ? TypeNode::null() : curp;
      d_preTCache[cur] = curp;
      if (!curp.isNull())
      {
        visit.push_back(cur);
        visit.push_back(curp);
      }
      else
      {
        if (cur.getNumChildren() == 0)
        {
          TypeNode ret = postConvertType(cur);
          addToTypeCache(cur, ret);
        }
        else
        {
          visit.push_back(cur);
          visit.insert(visit.end(), cur.begin(), cur.end());
        }
      }
    }
    else if (it->second.isNull())
    {
      it = d_preTCache.find(cur);
      Assert(it != d_preTCache.end());
      if (!it->second.isNull())
      {
        // it converts to what its prewrite converts to
        Assert(d_tcache.find(it->second) != d_tcache.end());
        TypeNode ret = d_tcache[it->second];
        addToTypeCache(cur, ret);
      }
      else
      {
        TypeNode ret = cur;
        // reconstruct using a node builder, which seems to be required for
        // type nodes.
        NodeBuilder nb(ret.getKind());
        // there are no parameterized types
        Assert (ret.getMetaKind() != kind::metakind::PARAMETERIZED);
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
        Trace("nconv-debug") << cur << " <- " << ret << std::endl;
        // run the callback for the current application
        TypeNode cret = postConvertType(ret);
        if (!cret.isNull())
        {
          ret = cret;
        }
        Trace("nconv-debug")
            << cur << " <- " << ret << " (post-convert)" << std::endl;
        addToTypeCache(cur, ret);
      }
    }
  } while (!visit.empty());
  Assert(d_tcache.find(tn) != d_tcache.end());
  Assert(!d_tcache.find(tn)->second.isNull());
  Trace("nconv-debug") << "NodeConverter::convertType: returns " << d_tcache[tn]
                       << std::endl;
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

Node NodeConverter::postConvertUntyped(Node orig,
                                       const std::vector<Node>& terms,
                                       bool termsChanged)
{
  return Node::null();
}

TypeNode NodeConverter::preConvertType(TypeNode tn) { return TypeNode::null(); }
TypeNode NodeConverter::postConvertType(TypeNode tn)
{
  return TypeNode::null();
}
bool NodeConverter::shouldTraverse(Node n) { return true; }

}  // namespace cvc5::internal
