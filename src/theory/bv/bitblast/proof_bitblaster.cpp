/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A bit-blaster wrapper around BBSimple for proof logging.
 */
#include "theory/bv/bitblast/proof_bitblaster.h"

#include <unordered_set>

#include "proof/conv_proof_generator.h"
#include "theory/bv/bitblast/bitblast_proof_generator.h"
#include "theory/theory_model.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

BBProof::BBProof(Env& env, TheoryState* state, bool fineGrained)
    : EnvObj(env),
      d_bb(new NodeBitblaster(env, state)),
      d_tcontext(new TheoryLeafTermContext(theory::THEORY_BV)),
      d_tcpg(new TConvProofGenerator(
          env,
          nullptr,
          /* ONCE to visit each term only once, post-order.  FIXPOINT
           * could lead to infinite loops due to terms being rewritten
           * to terms that contain themselves */
          TConvPolicy::ONCE,
          /* STATIC to get the same ProofNode for a shared subterm. */
          TConvCachePolicy::STATIC,
          "BBProof::TConvProofGenerator",
          d_tcontext.get(),
          false)),
      d_bbpg(new BitblastProofGenerator(env, d_tcpg.get())),
      d_recordFineGrainedProofs(fineGrained)
{
}

BBProof::~BBProof() {}

void BBProof::bbAtom(TNode node)
{
  bool fineProofs = isProofsEnabled() && d_recordFineGrainedProofs;

  /* Bit-blasting bit-vector atoms consists of 3 steps:
   *   1. rewrite the atom
   *   2. bit-blast the rewritten atom
   *   3. rewrite the resulting bit-blasted term
   *
   * This happens in a single call to d_bb->bbAtom(...). When we record
   * fine-grained proofs, we explicitly record the above 3 steps.
   *
   * Note: The below post-order traversal corresponds to the recursive
   * bit-blasting of bit-vector terms that happens implicitly when calling the
   * corresponding bit-blasting strategy in d_bb->bbAtom(...).
   */
  if (fineProofs)
  {
    std::vector<TNode> visit;
    std::unordered_set<TNode> visited;
    NodeManager* nm = NodeManager::currentNM();

    // post-rewrite atom
    Node rwNode = rewrite(node);

    // Post-order traversal of `rwNode` to make sure that all subterms are
    // bit-blasted and recorded.
    visit.push_back(rwNode);
    while (!visit.empty())
    {
      TNode n = visit.back();
      if (hasBBAtom(n) || hasBBTerm(n))
      {
        visit.pop_back();
        continue;
      }

      if (visited.find(n) == visited.end())
      {
        visited.insert(n);
        if (!Theory::isLeafOf(n, theory::THEORY_BV))
        {
          visit.insert(visit.end(), n.begin(), n.end());
        }
      }
      else
      {
        /* Handle BV theory leafs as variables, i.e., apply the BITVECTOR_BITOF
         * operator to each bit of `n`. */
        if (Theory::isLeafOf(n, theory::THEORY_BV) && !n.isConst())
        {
          Bits bits;
          d_bb->makeVariable(n, bits);

          Node bbt = nm->mkNode(kind::BITVECTOR_BB_TERM, bits);
          d_bbMap.emplace(n, bbt);
          d_tcpg->addRewriteStep(
              n, bbt, PfRule::BV_BITBLAST_STEP, {}, {n.eqNode(bbt)});
        }
        else if (n.getType().isBitVector())
        {
          Bits bits;
          d_bb->bbTerm(n, bits);

          Node bbt = nm->mkNode(kind::BITVECTOR_BB_TERM, bits);
          Node rbbt;
          if (n.isConst())
          {
            d_bbMap.emplace(n, bbt);
            rbbt = n;
          }
          else
          {
            d_bbMap.emplace(n, bbt);
            rbbt = reconstruct(n);
          }
          d_tcpg->addRewriteStep(
              rbbt, bbt, PfRule::BV_BITBLAST_STEP, {}, {rbbt.eqNode(bbt)});
        }
        else
        {
          Assert(n == rwNode);
        }
        visit.pop_back();
      }
    }

    /* Bit-blast given rewritten bit-vector atom `node`.
     * Note: This will pre and post-rewrite and store it in the bit-blasting
     * cache. */
    d_bb->bbAtom(node);
    Node result = d_bb->getStoredBBAtom(node);

    // Retrieve bit-blasted `rwNode` without post-rewrite.
    Node bbt = rwNode.getKind() == kind::CONST_BOOLEAN
                       || rwNode.getKind() == kind::BITVECTOR_BITOF
                   ? rwNode
                   : d_bb->applyAtomBBStrategy(rwNode);

    Node rbbt = reconstruct(rwNode);

    d_tcpg->addRewriteStep(
        rbbt, bbt, PfRule::BV_BITBLAST_STEP, {}, {rbbt.eqNode(bbt)});

    d_bbpg->addBitblastStep(node, bbt, node.eqNode(result));
  }
  else
  {
    d_bb->bbAtom(node);

    /* Record coarse-grain bit-blast proof step. */
    if (isProofsEnabled() && !d_recordFineGrainedProofs)
    {
      Node bbt = getStoredBBAtom(node);
      d_bbpg->addBitblastStep(Node(), Node(), node.eqNode(bbt));
    }
  }
}

Node BBProof::reconstruct(TNode t)
{
  NodeManager* nm = NodeManager::currentNM();

  std::vector<Node> children;
  if (t.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    children.push_back(t.getOperator());
  }
  for (const auto& child : t)
  {
    children.push_back(d_bbMap.at(child));
  }
  return nm->mkNode(t.getKind(), children);
}

bool BBProof::hasBBAtom(TNode atom) const { return d_bb->hasBBAtom(atom); }

bool BBProof::hasBBTerm(TNode atom) const { return d_bb->hasBBTerm(atom); }

Node BBProof::getStoredBBAtom(TNode node)
{
  return d_bb->getStoredBBAtom(node);
}

void BBProof::getBBTerm(TNode node, Bits& bits) const
{
  d_bb->getBBTerm(node, bits);
}

bool BBProof::collectModelValues(TheoryModel* m,
                                 const std::set<Node>& relevantTerms)
{
  return d_bb->collectModelValues(m, relevantTerms);
}

BitblastProofGenerator* BBProof::getProofGenerator() { return d_bbpg.get(); }

bool BBProof::isProofsEnabled() const { return d_env.isTheoryProofProducing(); }

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
