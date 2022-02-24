/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

#include "expr/node_manager_attributes.h"
#include "preprocessing/assertion_pipeline.h"
#include "proof/conv_proof_generator.h"
#include "smt/env.h"
#include "smt/solver_engine.h"
#include "theory/rewriter.h"
#include "theory/theory.h"
#include "util/resource_manager.h"

using namespace cvc5::preprocessing;
using namespace cvc5::theory;
using namespace cvc5::kind;

namespace cvc5 {
namespace smt {

ExpandDefs::ExpandDefs(Env& env) : EnvObj(env), d_tpg(nullptr) {}

ExpandDefs::~ExpandDefs() {}

Node ExpandDefs::expandDefinitions(TNode n,
                                   std::unordered_map<Node, Node>& cache)
{
  TrustNode trn = expandDefinitions(n, cache, nullptr);
  return trn.isNull() ? Node(n) : trn.getNode();
}

TrustNode ExpandDefs::expandDefinitions(TNode n,
                                        std::unordered_map<Node, Node>& cache,
                                        TConvProofGenerator* tpg)
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
      // we can short circuit (variable) leaves
      if (n.isVar())
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
        if (tpg != nullptr)
        {
          tpg->addRewriteStep(
              n, node, trn.getGenerator(), true, PfRule::THEORY_EXPAND_DEF);
        }
      }
      else
      {
        node = n;
      }
      // the partial functions can fall through, in which case we still
      // consider their children
      worklist.push(std::make_tuple(
          Node(n), node, true));  // Original and rewritten result

      for (size_t i = 0; i < node.getNumChildren(); ++i)
      {
        worklist.push(
            std::make_tuple(node[i],
                            node[i],
                            false));  // Rewrite the children of the result only
      }
    }
    else
    {
      // Working upwards
      // Reconstruct the node from it's (now rewritten) children on the stack

      Debug("expand") << "cons : " << node << std::endl;
      if (node.getNumChildren() > 0)
      {
        // cout << "cons : " << node << std::endl;
        NodeBuilder nb(node.getKind());
        if (node.getMetaKind() == metakind::PARAMETERIZED)
        {
          Debug("expand") << "op   : " << node.getOperator() << std::endl;
          // cout << "op   : " << node.getOperator() << std::endl;
          nb << node.getOperator();
        }
        for (size_t i = 0, nchild = node.getNumChildren(); i < nchild; ++i)
        {
          Assert(!result.empty());
          Node expanded = result.top();
          result.pop();
          // cout << "exchld : " << expanded << std::endl;
          Debug("expand") << "exchld : " << expanded << std::endl;
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

  Node res = result.top();

  if (res == orig)
  {
    return TrustNode::null();
  }
  return TrustNode::mkTrustRewrite(orig, res, tpg);
}

void ExpandDefs::enableProofs()
{
  // initialize if not done already
  if (d_tpg == nullptr)
  {
    Assert(d_env.getProofNodeManager() != nullptr);
    d_tpg.reset(new TConvProofGenerator(d_env.getProofNodeManager(),
                                        d_env.getUserContext(),
                                        TConvPolicy::FIXPOINT,
                                        TConvCachePolicy::NEVER,
                                        "ExpandDefs::TConvProofGenerator",
                                        nullptr,
                                        true));
  }
}

}  // namespace smt
}  // namespace cvc5
