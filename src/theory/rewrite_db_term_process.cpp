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

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

Node RewriteDbTermProcess::toInternal(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<Node, Node, NodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = d_internal.find(cur);

    if (it == d_internal.end())
    {
      d_internal[cur] = Node::null();
      visit.push_back(cur);
      for (const Node& cn : cur)
      {
        visit.push_back(cn);
      }
    }
    else if (it->second.isNull())
    {
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
        it = d_internal.find(cn);
        Assert(it != d_internal.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      Node ret;
      Kind ck = cur.getKind();
      if (ck == CONST_STRING)
      {
        // "ABC" is (str.++ "A" (str.++ "B" "C"))
        const std::vector<unsigned>& vec = cur.getConst<String>().getVec();
        if (vec.size() <= 1)
        {
          ret = cur;
        }
        else
        {
          std::vector<unsigned> v(vec.begin(), vec.end());
          std::reverse(v.begin(), v.end());
          std::vector<unsigned> tmp;
          tmp.push_back(v[0]);
          ret = nm->mkConst(String(tmp));
          tmp.pop_back();
          for (unsigned i = 1, size = v.size(); i < size; i++)
          {
            tmp.push_back(v[i]);
            ret = nm->mkNode(STRING_CONCAT, nm->mkConst(String(tmp)), ret);
            tmp.pop_back();
          }
        }
      }
      else if (ck == UMINUS)
      {
        if (children[0].isConst())
        {
          ret = nm->mkConst(-children[0].getConst<Rational>());
        }
      }
      else if (ExprManager::isNAryKind(ck) && children.size() >= 2)
      {
        Assert(cur.getMetaKind() != kind::metakind::PARAMETERIZED);
        // convert to binary
        std::reverse(children.begin(), children.end());
        ret = children[0];
        for (unsigned i = 1, nchild = children.size(); i < nchild; i++)
        {
          ret = nm->mkNode(ck, children[i], ret);
        }
      }
      if (ret.isNull())
      {
        if (childChanged)
        {
          ret = nm->mkNode(ck, children);
        }
        else
        {
          ret = cur;
        }
      }
      d_internal[cur] = ret;
    }
  } while (!visit.empty());
  Assert(d_internal.find(n) != d_internal.end());
  Assert(!d_internal.find(n)->second.isNull());
  return d_internal[n];
}

Node RewriteDbTermProcess::toExternal(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<Node, Node, NodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = d_external.find(cur);

    if (it == d_external.end())
    {
      d_external[cur] = Node::null();
      visit.push_back(cur);
      for (const Node& cn : cur)
      {
        visit.push_back(cn);
      }
    }
    else if (it->second.isNull())
    {
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
        it = d_external.find(cn);
        Assert(it != d_external.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      Node ret;
      Kind ck = cur.getKind();
      if (ExprManager::isNAryKind(ck))
      {
        Assert(children.size() == 2);
        if (children[1].getKind() == ck)
        {
          // flatten to n-ary
          Node cc = children[1];
          children.pop_back();
          for (const Node& ccc : cc)
          {
            children.push_back(ccc);
          }
          ret = nm->mkNode(ck, children);
        }
        else if (children[1].getKind() == CONST_STRING
                 && children[0].getKind() == CONST_STRING)
        {
          // flatten (non-empty) constants
          const std::vector<unsigned>& v0 =
              children[0].getConst<String>().getVec();
          const std::vector<unsigned>& v1 =
              children[1].getConst<String>().getVec();
          if (v0.size() == 1 && !v1.empty())
          {
            std::vector<unsigned> vres;
            vres.push_back(v0[0]);
            vres.insert(vres.end(), v1.begin(), v1.end());
            ret = nm->mkConst(String(vres));
          }
        }
      }
      else if (childChanged)
      {
        ret = nm->mkNode(ck, children);
      }
      if (ret.isNull())
      {
        ret = cur;
      }
      d_external[cur] = ret;
    }
  } while (!visit.empty());
  Assert(d_external.find(n) != d_external.end());
  Assert(!d_external.find(n)->second.isNull());
  return d_external[n];
}

}  // namespace theory
}  // namespace CVC4
