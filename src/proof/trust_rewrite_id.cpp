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
 * Implementation of trust identifier
 */

#include "proof/trust_rewrite_id.h"

#include "proof/proof_checker.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

const char* toString(TrustRewriteId id)
{
  switch (id)
  {
#define TRUST_REWRITE_ID_CASE(name) \
  case TrustRewriteId::name: return #name;
    TRUST_REWRITE_ID_CASE(NONE)
    TRUST_REWRITE_ID_CASE(BV_UMULO_ELIMINATE)
    TRUST_REWRITE_ID_CASE(BV_SMULO_ELIMINATE)
    TRUST_REWRITE_ID_CASE(BV_FLATTEN_ASSOC_COMMUTE)
    TRUST_REWRITE_ID_CASE(BV_FLATTEN_ASSOC_COMMUTE_NO_DUPLICATES)
    TRUST_REWRITE_ID_CASE(BV_ADD_COMBINE_LIKE_TERMS)
    TRUST_REWRITE_ID_CASE(BV_MULT_SIMPLIFY)
    TRUST_REWRITE_ID_CASE(BV_SOLVE_EQ)
    TRUST_REWRITE_ID_CASE(BV_BITWISE_EQ)
    TRUST_REWRITE_ID_CASE(BV_BITWISE_SLICING)
  };
}

std::ostream& operator<<(std::ostream& out, TrustRewriteId id)
{
  out << toString(id);
  return out;
}

Node mkTrustRewriteId(TrustRewriteId id)
{
  return NodeManager::currentNM()->mkConstInt(
      Rational(static_cast<uint32_t>(id)));
}

bool getTrustRewriteId(TNode n, TrustRewriteId& i)
{
  uint32_t index;
  if (!ProofRuleChecker::getUInt32(n, index))
  {
    return false;
  }
  i = static_cast<TrustRewriteId>(index);
  return true;
}

}  // namespace cvc5::internal
