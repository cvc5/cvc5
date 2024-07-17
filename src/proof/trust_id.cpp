/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of trust identifier
 */

#include "proof/trust_id.h"

#include "proof/proof_checker.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

const char* toString(TrustId id)
{
  switch (id)
  {
    case TrustId::NONE: return "NONE";
    case TrustId::THEORY_LEMMA: return "THEORY_LEMMA";
    case TrustId::THEORY_INFERENCE: return "THEORY_INFERENCE";
    case TrustId::PREPROCESS: return "PREPROCESS";
    case TrustId::PREPROCESS_LEMMA: return "PREPROCESS_LEMMA";
    case TrustId::PP_STATIC_REWRITE: return "PP_STATIC_REWRITE";
    case TrustId::THEORY_PREPROCESS: return "THEORY_PREPROCESS";
    case TrustId::THEORY_PREPROCESS_LEMMA: return "THEORY_PREPROCESS_LEMMA";
    case TrustId::THEORY_EXPAND_DEF: return "THEORY_EXPAND_DEF";
    case TrustId::ARITH_NL_COVERING_DIRECT: return "ARITH_NL_COVERING_DIRECT";
    case TrustId::ARITH_NL_COVERING_RECURSIVE:
      return "ARITH_NL_COVERING_RECURSIVE";
    case TrustId::EXT_THEORY_REWRITE: return "EXT_THEORY_REWRITE";
    case TrustId::REWRITE_NO_ELABORATE: return "REWRITE_NO_ELABORATE";
    case TrustId::FLATTENING_REWRITE: return "FLATTENING_REWRITE";
    case TrustId::SUBS_NO_ELABORATE: return "SUBS_NO_ELABORATE";
    case TrustId::SUBS_MAP: return "SUBS_MAP";
    case TrustId::SUBS_EQ: return "SUBS_EQ";
    case TrustId::ARITH_PRED_CAST_TYPE: return "ARITH_PRED_CAST_TYPE";
    case TrustId::QUANTIFIERS_PREPROCESS: return "QUANTIFIERS_PREPROCESS";
    case TrustId::SUBTYPE_ELIMINATION: return "SUBTYPE_ELIMINATION";
    case TrustId::MACRO_THEORY_REWRITE_RCONS:
      return "MACRO_THEORY_REWRITE_RCONS";
    case TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE:
      return "MACRO_THEORY_REWRITE_RCONS_SIMPLE";
    default: return "TrustId::Unknown";
  };
}

std::ostream& operator<<(std::ostream& out, TrustId id)
{
  out << toString(id);
  return out;
}

Node mkTrustId(TrustId id)
{
  return NodeManager::currentNM()->mkConstInt(
      Rational(static_cast<uint32_t>(id)));
}

bool getTrustId(TNode n, TrustId& i)
{
  uint32_t index;
  if (!ProofRuleChecker::getUInt32(n, index))
  {
    return false;
  }
  i = static_cast<TrustId>(index);
  return true;
}

}  // namespace cvc5::internal
