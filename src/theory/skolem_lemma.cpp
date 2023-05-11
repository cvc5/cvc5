/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The skolem lemma utility.
 */

#include "theory/skolem_lemma.h"

#include "expr/skolem_manager.h"

namespace cvc5::internal {
namespace theory {

SkolemLemma::SkolemLemma(TrustNode lem, Node k) : d_lemma(lem), d_skolem(k)
{
  Assert(lem.getKind() == TrustNodeKind::LEMMA);
}

Node SkolemLemma::getProven() const { return d_lemma.getProven(); }

}  // namespace theory
}  // namespace cvc5::internal
