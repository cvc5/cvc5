/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of expand definitions for an SMT engine.
 */

#include "smt/expand_definitions.h"

#include <stack>
#include <utility>

#include "preprocessing/assertion_pipeline.h"
#include "smt/env.h"
#include "theory/rewriter.h"
#include "theory/theory.h"
#include "util/resource_manager.h"

using namespace cvc5::internal::preprocessing;
using namespace cvc5::internal::theory;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace smt {

ExpandDefs::ExpandDefs(Env& env) : EnvObj(env) {}

ExpandDefs::~ExpandDefs() {}

Node ExpandDefs::expandDefinitions(TNode n,
                                   std::unordered_map<Node, Node>& cache)
{
  const TNode orig = n;
  std::stack<std::tuple<Node, Node, bool>> worklist;
  std::stack<Node> result;
  worklist.push(std::make_tuple(Node(n), Node(n), false));
  // The worklist is made of triples, each is input / original node then the
  // output / rewritten node and finally a flag tracking whether the children
  // have been explored (i.e. if this is a downward or upward pass).

  ResourceManager* rm = d_env.getResourceManager();
  Rewriter* rr = d_env.getRewriter();
  do
  {
    rm->spendResource(Resource::PreprocessStep);

    // n is the input / original
    // node is the output / result
    Node node;
    bool childrenPushed;
    std::tie(n, node, childrenPushed) = worklist.top();
    worklist.pop();

    // Working downwards
    if (!childrenPushed)
    {
      // we can short circuit (variable) leaves and closures, whose bodies
      // are not preprocessed
      if (n.isVar() || n.isClosure())
      {
        // don't bother putting in the cache
        result.push(n);
        continue;
      }

      // maybe it's in the cache
      std::unordered_map<Node, Node>::iterator cacheHit = cache.find(n);
      if (cacheHit != cache.end())
      {
        TNode ret = (*cacheHit).second;
        result.push(ret.isNull() ? n : ret);
        continue;
      }
      theory::TheoryId tid = d_env.theoryOf(node);
      theory::TheoryRewriter* tr = rr->getTheoryRewriter(tid);

      Assert(tr != NULL);
      TrustNode trn = tr->expandDefinition(n);
      if (!trn.isNull())
      {
        node = trn.getNode();
      }
      else
      {
        node = n;
      }
      // the partial functions can fall through, in which case we still
      // consider their children
      worklist.push(std::make_tuple(
          Node(n), node, true));  // Original and rewritten result

      for (const Node& nc : node)
      {
        // Rewrite the children of the result only
        worklist.push(std::make_tuple(nc, nc, false));
      }
    }
    else
    {
      // Working upwards
      // Reconstruct the node from it's (now rewritten) children on the stack

      Trace("expand") << "cons : " << node << std::endl;
      if (node.getNumChildren() > 0)
      {
        // cout << "cons : " << node << std::endl;
        NodeBuilder nb(node.getKind());
        if (node.getMetaKind() == metakind::PARAMETERIZED)
        {
          Trace("expand") << "op   : " << node.getOperator() << std::endl;
          // cout << "op   : " << node.getOperator() << std::endl;
          nb << node.getOperator();
        }
        for (size_t i = 0, nchild = node.getNumChildren(); i < nchild; ++i)
        {
          Assert(!result.empty());
          Node expanded = result.top();
          result.pop();
          // cout << "exchld : " << expanded << std::endl;
          Trace("expand") << "exchld : " << expanded << std::endl;
          nb << expanded;
        }
        node = nb;
      }
      // Only cache once all subterms are expanded
      cache[n] = n == node ? Node::null() : node;
      result.push(node);
    }
  } while (!worklist.empty());

  AlwaysAssert(result.size() == 1);

  return result.top();
}

}  // namespace smt
}  // namespace cvc5::internal
