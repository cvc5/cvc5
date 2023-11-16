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

#include "proof/theory_rewrite_id.h"

#include "proof/proof_checker.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

const char* toString(TheoryRewriteId id)
{
  switch (id)
  {
#define THEORY_REWRITE_ID_CASE(name) \
  case TheoryRewriteId::name: return #name;
    THEORY_REWRITE_ID_CASE(NONE)
    THEORY_REWRITE_ID_CASE(BV_UMULO_ELIMINATE)
    THEORY_REWRITE_ID_CASE(BV_SMULO_ELIMINATE)
    THEORY_REWRITE_ID_CASE(BV_FLATTEN_ASSOC_COMMUTE)
    THEORY_REWRITE_ID_CASE(BV_FLATTEN_ASSOC_COMMUTE_NO_DUPLICATES)
    THEORY_REWRITE_ID_CASE(BV_ADD_COMBINE_LIKE_TERMS)
    THEORY_REWRITE_ID_CASE(BV_MULT_SIMPLIFY)
    THEORY_REWRITE_ID_CASE(BV_SOLVE_EQ)
    THEORY_REWRITE_ID_CASE(BV_BITWISE_EQ)
    THEORY_REWRITE_ID_CASE(BV_BITWISE_SLICING)
    default: return "TrustTheoryId::Unknown";
  };
}

std::ostream& operator<<(std::ostream& out, TheoryRewriteId id)
{
  out << toString(id);
  return out;
}

Node mkTheoryRewriteId(TheoryRewriteId id)
{
  return NodeManager::currentNM()->mkConstInt(
      Rational(static_cast<uint32_t>(id)));
}

bool getTheoryRewriteId(TNode n, TheoryRewriteId& i)
{
  uint32_t index;
  if (!ProofRuleChecker::getUInt32(n, index))
  {
    return false;
  }
  i = static_cast<TheoryRewriteId>(index);
  return true;
}

}  // namespace cvc5::internal
