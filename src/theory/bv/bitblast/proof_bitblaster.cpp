/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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
#include "theory/theory_model.h"

namespace cvc5 {
namespace theory {
namespace bv {

BBProof::BBProof(TheoryState* state, ProofNodeManager* pnm, bool fineGrained)
    : d_bb(new NodeBitblaster(state)),
      d_pnm(pnm),
      d_tcontext(new TheoryLeafTermContext(theory::THEORY_BV)),
      d_tcpg(pnm ? new TConvProofGenerator(
                 pnm,
                 nullptr,
                 /* ONCE to visit each term only once, post-order.  FIXPOINT
                  * could lead to infinite loops due to terms being rewritten
                  * to terms that contain themselves */
                 TConvPolicy::ONCE,
                 /* STATIC to get the same ProofNode for a shared subterm. */
                 TConvCachePolicy::STATIC,
                 "BBProof::TConvProofGenerator",
                 d_tcontext.get(),
                 false)
                 : nullptr),
      d_recordFineGrainedProofs(fineGrained)
{
}

BBProof::~BBProof() {}

void BBProof::bbAtom(TNode node)
{
  std::vector<TNode> visit;
  visit.push_back(node);
  std::unordered_set<TNode> visited;

  bool fpenabled = isProofsEnabled() && d_recordFineGrainedProofs;

  NodeManager* nm = NodeManager::currentNM();

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
      if (Theory::isLeafOf(n, theory::THEORY_BV) && !n.isConst())
      {
        Bits bits;
        d_bb->makeVariable(n, bits);
        if (fpenabled)
        {
          Node n_tobv = nm->mkNode(kind::BITVECTOR_BB_TERM, bits);
          d_bbMap.emplace(n, n_tobv);
          d_tcpg->addRewriteStep(n,
                                 n_tobv,
                                 PfRule::BV_BITBLAST_STEP,
                                 {},
                                 {n.eqNode(n_tobv)},
                                 false);
        }
      }
      else if (n.getType().isBitVector())
      {
        Bits bits;
        d_bb->bbTerm(n, bits);
        Kind kind = n.getKind();
        if (fpenabled)
        {
          Node n_tobv = nm->mkNode(kind::BITVECTOR_BB_TERM, bits);
          d_bbMap.emplace(n, n_tobv);
          Node c_tobv;
          if (n.isConst())
          {
            c_tobv = n;
          }
          else
          {
            std::vector<Node> children_tobv;
            if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
            {
              children_tobv.push_back(n.getOperator());
            }

            for (const auto& child : n)
            {
              children_tobv.push_back(d_bbMap.at(child));
            }
            c_tobv = nm->mkNode(kind, children_tobv);
          }
          d_tcpg->addRewriteStep(c_tobv,
                                 n_tobv,
                                 PfRule::BV_BITBLAST_STEP,
                                 {},
                                 {c_tobv.eqNode(n_tobv)},
                                 false);
        }
      }
      else
      {
        d_bb->bbAtom(n);
        if (fpenabled)
        {
          Node n_tobv = getStoredBBAtom(n);
          std::vector<Node> children_tobv;
          for (const auto& child : n)
          {
            children_tobv.push_back(d_bbMap.at(child));
          }
          Node c_tobv = nm->mkNode(n.getKind(), children_tobv);
          d_tcpg->addRewriteStep(c_tobv,
                                 n_tobv,
                                 PfRule::BV_BITBLAST_STEP,
                                 {},
                                 {c_tobv.eqNode(n_tobv)},
                                 false);
        }
      }
      visit.pop_back();
    }
  }
  /* Record coarse-grain bit-blast proof step. */
  if (isProofsEnabled() && !d_recordFineGrainedProofs)
  {
    Node node_tobv = getStoredBBAtom(node);
    d_tcpg->addRewriteStep(node,
                           node_tobv,
                           PfRule::BV_BITBLAST,
                           {},
                           {node.eqNode(node_tobv)},
                           false);
  }
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

TConvProofGenerator* BBProof::getProofGenerator() { return d_tcpg.get(); }

bool BBProof::isProofsEnabled() const { return d_pnm != nullptr; }

}  // namespace bv
}  // namespace theory
}  // namespace cvc5
