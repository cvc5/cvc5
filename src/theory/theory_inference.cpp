/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The theory inference utility.
 */

#include "theory/theory_inference.h"

#include "theory/theory_inference_manager.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {

SimpleTheoryLemma::SimpleTheoryLemma(InferenceId id, 
                                     Node n,
                                     LemmaProperty p,
                                     ProofGenerator* pg)
    : TheoryInference(id), d_node(n), d_property(p), d_pg(pg)
{
}

TrustNode SimpleTheoryLemma::processLemma(LemmaProperty& p)
{
  Assert(!d_node.isNull());
  p = d_property;
  return TrustNode::mkTrustLemma(d_node, d_pg);
}

SimpleTheoryInternalFact::SimpleTheoryInternalFact(InferenceId id,
                                                   Node conc,
                                                   Node exp,
                                                   ProofGenerator* pg)
    : TheoryInference(id), d_conc(conc), d_exp(exp), d_pg(pg)
{
}

Node SimpleTheoryInternalFact::processFact(std::vector<Node>& exp,
                                           ProofGenerator*& pg)
{
  exp.push_back(d_exp);
  pg = d_pg;
  return d_conc;
}

}  // namespace theory
}  // namespace cvc5::internal
