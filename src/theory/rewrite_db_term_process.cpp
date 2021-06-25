/*********************                                                        */
/*! \file rewrite_db_term_process.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of rewrite db term processor.
 **/

#include "theory/rewrite_db_term_process.h"

#include "expr/attribute.h"
#include "util/rational.h"
#include "util/string.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {

struct RdtpInternalAttributeId
{
};
typedef expr::Attribute<RdtpInternalAttributeId, Node> RdtpInternalAttribute;

Node RewriteDbTermProcess::toInternal(Node n)
{
  if (n.isNull())
  {
    return n;
  }
  Trace("rdtp-debug") << "RewriteDbTermProcess::toInternal: " << n << std::endl;
  RdtpInternalAttribute ria;
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      if (cur.hasAttribute(ria))
      {
        visited[cur] = cur.getAttribute(ria);
      }
      else
      {
        visited[cur] = Node::null();
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
        it = visited.find(cur.getOperator());
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cur.getOperator() != it->second;
        children.push_back(it->second);
      }
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      ret = computeInternal(ret);
      cur.setAttribute(ria, ret);
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

Node RewriteDbTermProcess::computeInternal(Node n)
{
  Kind ck = n.getKind();
  if (ck == CONST_STRING)
  {
    NodeManager* nm = NodeManager::currentNM();
    // "ABC" is (str.++ "A" (str.++ "B" "C"))
    const std::vector<unsigned>& vec = n.getConst<String>().getVec();
    if (vec.size() <= 1)
    {
      return n;
    }
    std::vector<unsigned> v(vec.begin(), vec.end());
    std::reverse(v.begin(), v.end());
    std::vector<unsigned> tmp;
    tmp.push_back(v[0]);
    Node ret = nm->mkConst(String(tmp));
    tmp.pop_back();
    for (unsigned i = 1, size = v.size(); i < size; i++)
    {
      tmp.push_back(v[i]);
      ret = nm->mkNode(STRING_CONCAT, nm->mkConst(String(tmp)), ret);
      tmp.pop_back();
    }
    return ret;
  }
  else if (ck == UMINUS)
  {
    if (n[0].isConst())
    {
      NodeManager* nm = NodeManager::currentNM();
      return nm->mkConst(-n[0].getConst<Rational>());
    }
  }
  else if (NodeManager::isNAryKind(ck) && n.getNumChildren() >= 2)
  {
    NodeManager* nm = NodeManager::currentNM();
    Assert(n.getMetaKind() != kind::metakind::PARAMETERIZED);
    // convert to binary
    std::vector<Node> children(n.begin(), n.end());
    std::reverse(children.begin(), children.end());
    Node ret = children[0];
    for (unsigned i = 1, nchild = n.getNumChildren(); i < nchild; i++)
    {
      ret = nm->mkNode(ck, children[i], ret);
    }
    return ret;
  }
  return n;
}

}  // namespace theory
}  // namespace cvc5
