/*********************                                                        */
/*! \file fun_def_evaluator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of techniques for evaluating terms with recursively
 ** defined functions.
 **/

#include "theory/quantifiers/fun_def_evaluator.h"

#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

FunDefEvaluator::FunDefEvaluator() {}

void FunDefEvaluator::assertDefinition(Node q)
{
  Trace("fd-eval") << "FunDefEvaluator: assertDefinition " << q << std::endl;
  Node h = QuantAttributes::getFunDefHead(q);
  if (h.isNull())
  {
    // not a function definition
    return;
  }
  // h possibly with zero arguments?
  Node f = h.hasOperator() ? h.getOperator() : h;
  Assert(d_funDefMap.find(f) == d_funDefMap.end())
      << "FunDefEvaluator::assertDefinition: function already defined";
  FunDefInfo& fdi = d_funDefMap[f];
  fdi.d_body = QuantAttributes::getFunDefBody(q);
  Assert(!fdi.d_body.isNull());
  fdi.d_args.insert(fdi.d_args.end(), q[0].begin(), q[0].end());
  Trace("fd-eval") << "FunDefEvaluator: function " << f << " is defined with "
                   << fdi.d_args << " / " << fdi.d_body << std::endl;
}

Node FunDefEvaluator::evaluate(Node n) const
{
  // should do standard rewrite before this call
  Assert(Rewriter::rewrite(n) == n);
  Trace("fd-eval") << "FunDefEvaluator: evaluate " << n << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::map<Node, FunDefInfo>::const_iterator itf;
  std::vector<TNode> visit;
  TNode cur;
  TNode curEval;
  Node f;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    Trace("fd-eval-debug") << "evaluate subterm " << cur << std::endl;

    if (it == visited.end())
    {
      if (cur.isConst())
      {
        Trace("fd-eval-debug") << "constant " << cur << std::endl;
        visited[cur] = cur;
      }
      else
      {
        Trace("fd-eval-debug") << "recurse " << cur << std::endl;
        visited[cur] = Node::null();
        visit.push_back(cur);
        for (const Node& cn : cur)
        {
          visit.push_back(cn);
        }
      }
    }
    else
    {
      curEval = it->second;
      if (curEval.isNull())
      {
        Trace("fd-eval-debug") << "from arguments " << cur << std::endl;
        Node ret = cur;
        bool childChanged = false;
        std::vector<Node> children;
        Kind ck = cur.getKind();
        // If a parameterized node that is not APPLY_UF (which is handled below,
        // we add it to the children vector.
        if (ck != APPLY_UF && cur.getMetaKind() == metakind::PARAMETERIZED)
        {
          children.push_back(cur.getOperator());
        }
        for (const Node& cn : cur)
        {
          it = visited.find(cn);
          Assert(it != visited.end());
          Assert(!it->second.isNull());
          childChanged = childChanged || cn != it->second;
          children.push_back(it->second);
        }
        if (cur.getKind() == APPLY_UF)
        {
          // need to evaluate it
          f = cur.getOperator();
          itf = d_funDefMap.find(f);
          if (itf == d_funDefMap.end())
          {
            Trace("fd-eval") << "FunDefEvaluator: no definition for " << f
                             << ", FAIL" << std::endl;
            return Node::null();
          }
          // get the function definition
          Node sbody = itf->second.d_body;
          const std::vector<Node>& args = itf->second.d_args;
          if (!args.empty())
          {
            // invoke it on arguments
            sbody = sbody.substitute(
                args.begin(), args.end(), children.begin(), children.end());
            // rewrite it
            sbody = Rewriter::rewrite(sbody);
          }
          // our result is the result of the body
          visited[cur] = sbody;
          // If its not constant, we push back self and the substituted body.
          // Thus, we evaluate the body first; our result will be the result of
          // evaluating the body.
          if (!sbody.isConst())
          {
            visit.push_back(cur);
            visit.push_back(sbody);
          }
        }
        else
        {
          if (childChanged)
          {
            ret = nm->mkNode(cur.getKind(), children);
            ret = Rewriter::rewrite(ret);
          }
          if (!ret.isConst())
          {
            Trace("fd-eval") << "FunDefEvaluator: non-constant subterm " << ret
                             << ", FAIL" << std::endl;
            // failed, possibly due to free variable
            return Node::null();
          }
          visited[cur] = ret;
        }
      }
      else if (!curEval.isConst())
      {
        Trace("fd-eval-debug") << "from body " << cur << std::endl;
        // we had to evaluate our body, which should have a definition now
        it = visited.find(curEval);
        Assert(it != visited.end());
        // our definition is the result of the body
        visited[cur] = it->second;
        Assert(it->second.isConst());
      }
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  Assert(visited.find(n)->second.isConst());
  Trace("fd-eval") << "FunDefEvaluator: return SUCCESS " << visited[n]
                   << std::endl;
  return visited[n];
}

bool FunDefEvaluator::hasDefinitions() const { return !d_funDefMap.empty(); }

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
