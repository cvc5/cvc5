/*********************                                                        */
/*! \file fun_def_evaluator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sort inference module
 **
 ** This class implements pre-process steps for admissible recursive function definitions (Reynolds et al IJCAR2016)
 **/

#include "theory/quantifiers/fun_def_evaluator.h"

#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {
  
FunDefEvaluator::FunDefEvaluator(){
  
}

void FunDefEvaluator::assertDefinition( Node q )
{
  
}

Node FunDefEvaluator::simplifyNode(Node n)
{
  Trace("fd-eval") << "FunDefEvaluator: simplify node " << n << std::endl;
  NodeManager * nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  TNode curEval;
  TNode f;
  visit.push_back(n);
  do {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end()) {
      if (cur.isConst())
      {
        visited[cur] = cur;
      }
      else
      {
        visited[cur] = Node::null();
        visit.push_back(cur);
        for (const Node& cn : cur) {
          visit.push_back(cn);
        }
      }
    } else {
      curEval = it->second;
      if (curEval.isNull()) 
      {
        Node ret = cur;
        bool childChanged = false;
        std::vector<Node> children;
        if (cur.getMetaKind() == metakind::PARAMETERIZED) 
        {
          children.push_back(cur.getOperator());
        }
        for (const Node& cn : cur) {
          it = visited.find(cn);
          Assert(it != visited.end());
          Assert(!it->second.isNull());
          childChanged = childChanged || cn != it->second;
          children.push_back(it->second);
        }
        if (cur.getKind()==APPLY_UF)
        {
          // need to evaluate it
          f = cur.getOperator();
          std::map< Node, FunDefInfo >::iterator it = d_funDefMap.find(f);
          if (it==d_funDefMap.end())
          {
            Trace("fd-eval") << "FunDefEvaluator: no definition for " << f << ", FAIL" << std::endl;
            return Node::null();
          }
          // get the function definition
          Node body = it->second.d_body;
          std::vector< Node >& args = it->second.d_args;
          // invoke it on arguments
          Node sbody = body.substitute(args.begin(),args.end(),children.begin(),children.end());
          // rewrite it
          sbody = Rewriter::rewrite(sbody);
          // our result is the result of the body
          visited[cur] = sbody;
          // If its not constant, we push back self and the substituted body.
          // Thus, we evaluate the body first; our result will be the result of
          // the body.
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
            Trace("fd-eval") << "FunDefEvaluator: non-constant subterm " << ret << ", FAIL" << std::endl;
            // failed, possibly due to free variable
            return Node::null();
          }
          visited[cur] = ret;
        }
      }
      else if (!curEval.isConst())
      {
        // we had to evaluate our body, which should have a definition now
        it = visited.find(curEval);
        Assert(it != visited.end());
        // our definition is the result of the body
        visited[cur] = it->second;
      }
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  Trace("fd-eval") << "FunDefEvaluator: return SUCCESS " << n << std::endl;
  return visited[n];
}

}
}
}
