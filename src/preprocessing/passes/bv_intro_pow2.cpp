/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Liana Hadarean, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The BvIntroPow2 preprocessing pass.
 *
 * Traverses the formula and applies the IsPowerOfTwo rewrite rule. This
 * preprocessing pass is particularly useful on QF_BV/pspace benchmarks and
 * can be enabled via option `--bv-intro-pow2`.
 */

#include "preprocessing/passes/bv_intro_pow2.h"

#include <unordered_map>

#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/bv/theory_bv_utils.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using NodeMap = std::unordered_map<Node, Node>;
using namespace cvc5::internal::theory;

BvIntroPow2::BvIntroPow2(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "bv-intro-pow2"){};

PreprocessingPassResult BvIntroPow2::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  std::unordered_map<Node, Node> cache;
  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Node cur = (*assertionsToPreprocess)[i];
    Node res = pow2Rewrite(cur, cache);
    if (res != cur)
    {
      res = rewrite(res);
      assertionsToPreprocess->replace(i, res);
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

bool BvIntroPow2::isPowerOfTwo(TNode node)
{
  if (node.getKind() != kind::EQUAL)
  {
    return false;
  }
  if (node[0].getKind() != kind::BITVECTOR_AND
      && node[1].getKind() != kind::BITVECTOR_AND)
  {
    return false;
  }
  if (!bv::utils::isZero(node[0]) && !bv::utils::isZero(node[1]))
  {
    return false;
  }

  TNode t = !bv::utils::isZero(node[0]) ? node[0] : node[1];
  if (t.getNumChildren() != 2) return false;
  TNode a = t[0];
  TNode b = t[1];
  if (bv::utils::getSize(t) < 2) return false;
  Node diff =
      rewrite(NodeManager::currentNM()->mkNode(kind::BITVECTOR_SUB, a, b));
  return (diff.isConst()
          && (bv::utils::isOne(diff) || bv::utils::isOnes(diff)));
}

Node BvIntroPow2::rewritePowerOfTwo(TNode node)
{
  NodeManager* nm = NodeManager::currentNM();
  TNode term = bv::utils::isZero(node[0]) ? node[1] : node[0];
  TNode a = term[0];
  TNode b = term[1];
  uint32_t size = bv::utils::getSize(term);
  Node diff = rewrite(nm->mkNode(kind::BITVECTOR_SUB, a, b));
  Assert(diff.isConst());
  Node one = bv::utils::mkOne(size);
  TNode x = diff == one ? a : b;
  Node sk = bv::utils::mkVar(size);
  Node sh = nm->mkNode(kind::BITVECTOR_SHL, one, sk);
  Node x_eq_sh = nm->mkNode(kind::EQUAL, x, sh);
  return x_eq_sh;
}

Node BvIntroPow2::pow2Rewrite(Node node, std::unordered_map<Node, Node>& cache)
{
  const auto& ci = cache.find(node);
  if (ci != cache.end())
  {
    Node incache = (*ci).second;
    return incache.isNull() ? node : incache;
  }

  Node res = Node::null();
  switch (node.getKind())
  {
    case kind::AND:
    {
      bool changed = false;
      std::vector<Node> children;
      for (unsigned i = 0, size = node.getNumChildren(); i < size; ++i)
      {
        Node child = node[i];
        Node found = pow2Rewrite(child, cache);
        changed = changed || (child != found);
        children.push_back(found);
      }
      if (changed)
      {
        res = NodeManager::currentNM()->mkNode(kind::AND, children);
      }
    }
    break;

    case kind::EQUAL:
      if (node[0].getType().isBitVector() && isPowerOfTwo(node))
      {
        res = rewritePowerOfTwo(node);
      }
      break;
    default: break;
  }

  cache.insert(std::make_pair(node, res));
  return res.isNull() ? node : res;
}

}  // namespace passes
}  // namespace preprocessing

}  // namespace cvc5::internal
