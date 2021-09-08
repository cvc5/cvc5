/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bitblast proof generator for generating bit-blast proof steps.
 */
#include "theory/bv/bitblast/bitblast_proof_generator.h"

#include "proof/conv_proof_generator.h"
#include "theory/rewriter.h"

namespace cvc5 {
namespace theory {
namespace bv {

BitblastProofGenerator::BitblastProofGenerator(ProofNodeManager* pnm,
                                               TConvProofGenerator* tcpg)
    : d_pnm(pnm), d_tcpg(tcpg)
{
}

std::shared_ptr<ProofNode> BitblastProofGenerator::getProofFor(Node eq)
{
  const auto& [t, bbt] = d_cache.at(eq);

  CDProof cdp(d_pnm);
  /* Coarse-grained bit-blast step. */
  if (t.isNull())
  {
    cdp.addStep(eq, PfRule::BV_BITBLAST, {}, {eq});
  }
  else
  {
    /* Fine-grained bit-blast step for bit-blasting bit-vector atoms (bbAtom()).
     * Bit-blasting atoms involves three steps:
     * 1) pre-rewrite: rewrite atom
     * 2) bit-blast rewritten atom
     * 3) post-rewrite: rewrite bit-blasted atom
     * bit-blasts and post-rewrites.
     */

    Node rwt = Rewriter::rewrite(t);

    std::vector<Node> transSteps;

    // Record pre-rewrite of bit-blasted term.
    if (t != rwt)
    {
      cdp.addStep(t.eqNode(rwt), PfRule::REWRITE, {}, {t});
      transSteps.push_back(t.eqNode(rwt));
    }

    // Record bit-blast step.
    cdp.addProof(d_tcpg->getProofFor(rwt.eqNode(bbt)));
    transSteps.push_back(rwt.eqNode(bbt));

    // Record post-rewrite of bit-blasted term.
    Node rwbbt = Rewriter::rewrite(bbt);
    if (bbt != rwbbt)
    {
      cdp.addStep(bbt.eqNode(rwbbt), PfRule::REWRITE, {}, {bbt});
      transSteps.push_back(bbt.eqNode(rwbbt));
    }

    if (transSteps.size() > 1)
    {
      cdp.addStep(eq, PfRule::TRANS, transSteps, {});
    }
  }

  return cdp.getProofFor(eq);
}

void BitblastProofGenerator::addBitblastStep(TNode t, TNode bbt, TNode eq)
{
  d_cache.emplace(eq, std::make_tuple(t, bbt));
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5
