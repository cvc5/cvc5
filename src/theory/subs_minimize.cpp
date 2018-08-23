/*********************                                                        */
/*! \file subs_minimize.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of subs_minimize
 **/

#include "theory/subs_minimize.h"

#include "theory/rewriter.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

SubstitutionMinimize::SubstitutionMinimize() {}

bool SubstitutionMinimize::find(Node n,
                                Node target,
                                const std::vector<Node>& vars,
                                const std::vector<Node>& subs,
                                std::vector<Node>& reqVars)
{
  NodeManager* nm = NodeManager::currentNM();

  // the value of each subterm in n under the substitution
  std::unordered_map<TNode, Node, TNodeHashFunction> value;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = value.find(cur);

    if (it == value.end())
    {
      if (cur.isVar())
      {
        const std::vector<Node>::const_iterator& it =
            std::find(vars.begin(), vars.end(), cur);
        if (it == vars.end())
        {
          value[cur] = cur;
        }
        else
        {
          ptrdiff_t pos = std::distance(vars.begin(), it);
          value[cur] = subs[pos];
        }
      }
      else
      {
        value[cur] = Node::null();
        visit.push_back(cur);
        if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
        {
          visit.push_back(cur.getOperator());
        }
        for (const Node& cn : cur)
        {
          visit.push_back(cn);
        }
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
        children.push_back(cn);
      }
      for (const Node& cn : children)
      {
        it = value.find(cn);
        Assert(it != value.end());
        Assert(!it->second.isNull());
        children.push_back(it->second);
      }
      ret = nm->mkNode(cur.getKind(), children);
      ret = Rewriter::rewrite(ret);
      value[cur] = ret;
    }
  } while (!visit.empty());
  Assert(value.find(n) != value.end());
  Assert(!value.find(n)->second.isNull());

  return false;
}

}  // namespace theory
}  // namespace CVC4
