/*********************                                                        */
/*! \file global_negate.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of global_negate
 **/

#include "theory/quantifiers/global_negate.h"
#include "theory/rewriter.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

void GlobalNegate::simplify(std::vector<Node>& assertions)
{
  NodeManager* nm = NodeManager::currentNM();
  Assert(!assertions.empty());

  Trace("cbqi-gn") << "Global negate : " << std::endl;
  // collect free variables in all assertions
  std::vector<Node> free_vars;
  std::vector<TNode> visit;
  std::unordered_set<TNode, TNodeHashFunction> visited;
  for (const Node& as : assertions)
  {
    Trace("cbqi-gn") << "  " << as << std::endl;
    TNode cur = as;
    // compute free variables
    visit.push_back(cur);
    do
    {
      cur = visit.back();
      visit.pop_back();
      if (visited.find(cur) == visited.end())
      {
        visited.insert(cur);
        if (cur.isVar() && cur.getKind() != BOUND_VARIABLE)
        {
          free_vars.push_back(cur);
        }
        for (const TNode& cn : cur)
        {
          visit.push_back(cn);
        }
      }
    } while (!visit.empty());
  }

  Node body;
  if (assertions.size() == 1)
  {
    body = assertions[0];
  }
  else
  {
    body = nm->mkNode(AND, assertions);
  }

  // do the negation
  body = body.negate();

  if (!free_vars.empty())
  {
    std::vector<Node> bvs;
    for (const Node& v : free_vars)
    {
      Node bv = nm->mkBoundVar(v.getType());
      bvs.push_back(bv);
    }

    body = body.substitute(
        free_vars.begin(), free_vars.end(), bvs.begin(), bvs.end());

    Node bvl = nm->mkNode(BOUND_VAR_LIST, bvs);

    body = nm->mkNode(FORALL, bvl, body);
  }

  Trace("cbqi-gn-debug") << "...got (pre-rewrite) : " << body << std::endl;
  body = Rewriter::rewrite(body);
  Trace("cbqi-gn") << "...got (post-rewrite) : " << body << std::endl;

  Node truen = nm->mkConst(true);
  for (unsigned i = 0, size = assertions.size(); i < size; i++)
  {
    if (i == 0)
    {
      assertions[i] = body;
    }
    else
    {
      assertions[i] = truen;
    }
  }
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
