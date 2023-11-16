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

#ifndef CVC5__PROOF__TRUST_REWRITE_ID_H
#define CVC5__PROOF__TRUST_REWRITE_ID_H

#include "expr/node.h"

namespace cvc5::internal {

/**
 * Identifiers for trusted steps in proofs.
 */
enum class TrustRewriteId : uint32_t
{
  NONE,
  BV_UMULO_ELIMINATE,
  BV_SMULO_ELIMINATE,
  BV_FLATTEN_ASSOC_COMMUTE,
  BV_FLATTEN_ASSOC_COMMUTE_NO_DUPLICATES,
  BV_ADD_COMBINE_LIKE_TERMS,
  BV_MULT_SIMPLIFY,
  BV_SOLVE_EQ,
  BV_BITWISE_EQ,
  BV_BITWISE_SLICING,

};
/** Converts a trust rewrite id to a string. */
const char* toString(TrustRewriteId id);
/** Write a trust rewrite id to out */
std::ostream& operator<<(std::ostream& out, TrustRewriteId id);
/** Make a trust rewrite id node */
Node mkTrustRewriteId(TrustRewriteId id);
/** get a trust identifier from a node, return false if we fail */
bool getTrustRewriteId(TNode n, TrustRewriteId& i);

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__TRUST_REWRITE_ID_H */
