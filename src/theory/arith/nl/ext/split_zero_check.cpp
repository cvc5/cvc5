/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of split zero check.
 */

#include "theory/arith/nl/ext/split_zero_check.h"

#include "expr/node.h"
#include "proof/proof.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/ext/ext_state.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/rewriter.h"

namespace cvc5 {
namespace theory {
namespace arith {
namespace nl {

SplitZeroCheck::SplitZeroCheck(ExtState* data)
    : d_data(data), d_zero_split(d_data->d_ctx)
{
}

void SplitZeroCheck::check()
{
  for (unsigned i = 0; i < d_data->d_ms_vars.size(); i++)
  {
    Node v = d_data->d_ms_vars[i];
    if (d_zero_split.insert(v))
    {
      Node eq = Rewriter::rewrite(v.eqNode(d_data->d_zero));
      Node lem = eq.orNode(eq.negate());
      CDProof* proof = nullptr;
      if (d_data->isProofEnabled())
      {
        proof = d_data->getProof();
        proof->addStep(lem, PfRule::SPLIT, {}, {eq});
      }
      d_data->d_im.addPendingPhaseRequirement(eq, true);
      d_data->d_im.addPendingLemma(
          lem, InferenceId::ARITH_NL_SPLIT_ZERO, proof);
    }
  }
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5
