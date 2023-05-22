/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

namespace cvc5::internal {
namespace theory {
namespace bv {

BitblastProofGenerator::BitblastProofGenerator(Env& env,
                                               TConvProofGenerator* tcpg)
    : EnvObj(env), d_tcpg(tcpg)
{
}

std::shared_ptr<ProofNode> BitblastProofGenerator::getProofFor(Node eq)
{
  const auto& [t, bbt] = d_cache.at(eq);

  CDProof cdp(d_env);
  /* Coarse-grained bit-blast step. */
  if (t.isNull())
  {
    cdp.addStep(eq, PfRule::BV_BITBLAST, {}, {eq});
  }
  else
  {
    /* Fine-grained bit-blast step for bit-blasting bit-vector atoms (bbAtom()).
     * Bit-blasting atoms involves three steps:
     *
     * 1) pre-rewrite: rewrite atom
     * 2) bit-blast rewritten atom
     * 3) post-rewrite: rewrite bit-blasted atom
     *
     * The CDProof is used for constructing the following proof of
     * transitivity:
     *
     * --------- RW  ----------- BB ------------- RW
     *  t = rwt       rwt = bbt      bbt = rwbbt
     * ---------------------------------------------- TRANS
     *                  t = rwbbt
     *
     *
     * where BB corresponds to the conversion proof PI_1 and a bit-blasting
     * step.  Note that if t and bbt remain the same after rewriting the
     * transitivity proof is not needed.
     *
     * The full proof tree is as follows:
     *
     * ------------------- RW        ------------------ BB ------------ RW
     *  P(x,y) = P(x',y')      PI_1   P(x'',y'') = bbt      bbt = rwbbt
     * ------------------------------------------------------------------ TRANS
     *                     P(x,y) = rwbbt
     *
     *
     *      PI_1 :=     -------- BB* ---------- BB*
     *                   x' = x''     y' = y''
     *                  ----------------------- CONG
     *                   P(x',y') = P(x'',y'')
     *
     *
     * where P is an arbitrary bit-vector atom and t := P(x,y), rwt := P(x',y').
     * BB* corresponds to recursively applying bit-blasting to all the
     * sub-terms and recording these bit-blast steps in the conversion proof.
     */

    Node rwt = rewrite(t);

    std::vector<Node> transSteps;

    // Record pre-rewrite of bit-vector atom.
    if (t != rwt)
    {
      cdp.addStep(t.eqNode(rwt), PfRule::REWRITE, {}, {t});
      transSteps.push_back(t.eqNode(rwt));
    }

    // Add bit-blast proof from conversion generator.
    cdp.addProof(d_tcpg->getProofFor(rwt.eqNode(bbt)));
    transSteps.push_back(rwt.eqNode(bbt));

    // Record post-rewrite of bit-blasted term.
    Node rwbbt = rewrite(bbt);
    if (bbt != rwbbt)
    {
      cdp.addStep(bbt.eqNode(rwbbt), PfRule::REWRITE, {}, {bbt});
      transSteps.push_back(bbt.eqNode(rwbbt));
    }

    // If pre- and post-rewrite did not apply, no rewrite steps need to be
    // recorded and the given equality `eq` is already justified by the proof
    // given by the conversion proof generator.
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
}  // namespace cvc5::internal
