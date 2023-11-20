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
 * Trust identifier enumeration
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__TRUST_ID_H
#define CVC5__PROOF__TRUST_ID_H

#include "expr/node.h"

namespace cvc5::internal {

/**
 * Identifiers for trusted steps in proofs.
 */
enum class TrustId : uint32_t
{
  NONE,
  /** A lemma sent by a theory without a proof */
  THEORY_LEMMA,
  /** An internal inference made by a theory without a proof */
  THEORY_INFERENCE,
  /** A rewrite of the input formula by a preprocessing pass without a proof */
  PREPROCESS,
  /** A lemma added during preprocessing without a proof */
  PREPROCESS_LEMMA,
  /** A rewrite of the input formula made by a theory during preprocessing
     without a proof */
  THEORY_PREPROCESS,
  /** A lemma added during theory-preprocessing without a proof */
  THEORY_PREPROCESS_LEMMA,
  /** A expanding of definitions of the input formula made without a proof */
  THEORY_EXPAND_DEF,
  /** An axiom for an introduced witness term without a corresponding proof */
  WITNESS_AXIOM,
  /** A rewrite whose proof could not be elaborated */
  REWRITE_NO_ELABORATE,
  /** A flattening rewrite in an equality engine proof */
  FLATTENING_REWRITE,
  /** A proof of an applied substitution that could not be no elaborate */
  SUBS_NO_ELABORATE,
  /** A proof of an applied substitution that could not be reconstructed during
     solving */
  SUBS_MAP,
  /** A proof of a substitution x=t that could not be shown by rewrite */
  SUBS_EQ,
  /** A quantifiers preprocessing step that was given without a proof */
  QUANTIFIERS_PREPROCESS,
};
/** Converts a trust id to a string. */
const char* toString(TrustId id);
/** Write a trust id to out */
std::ostream& operator<<(std::ostream& out, TrustId id);
/** Make a trust id node */
Node mkTrustId(TrustId id);
/** get a trust identifier from a node, return false if we fail */
bool getTrustId(TNode n, TrustId& i);

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__METHOD_ID_H */
