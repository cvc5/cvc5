/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The skolem lemma utility.
 */

#include "theory/skolem_lemma.h"

#include "expr/skolem_manager.h"

namespace cvc5 {
namespace theory {

SkolemLemma::SkolemLemma(TrustNode lem, Node k) : d_lemma(lem), d_skolem(k)
{
  Assert(lem.getKind() == TrustNodeKind::LEMMA);
}

SkolemLemma::SkolemLemma(Node k, ProofGenerator* pg) : d_lemma(), d_skolem(k)
{
  Node lem = getSkolemLemmaFor(k);
  d_lemma = TrustNode::mkTrustLemma(lem, pg);
}

Node SkolemLemma::getSkolemLemmaFor(Node k)
{
  Node w = SkolemManager::getWitnessForm(k);
  Assert(w.getKind() == kind::WITNESS);
  TNode tx = w[0][0];
  TNode tk = k;
  return w[1].substitute(tx, tk);
}

}  // namespace theory
}  // namespace cvc5
