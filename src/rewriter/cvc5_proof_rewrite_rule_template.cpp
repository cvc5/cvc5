/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Hans-Jörg Schurr, Leni Aniva
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Generated proof rewrite rules.
 */

#include "base/check.h"
#include "cvc5/cvc5_proof_rewrite_rule.h"

namespace cvc5 {

const char* toString(cvc5::ProofRewriteRule rule)
{
  switch (rule)
  {
    case ProofRewriteRule::NONE:
      return "NONE";
      // clang-format off
${printer}$
    default : Unreachable();
      // clang-format on
  }
}

std::ostream& operator<<(std::ostream& out, ProofRewriteRule rule)
{
  out << toString(rule);
  return out;
}

}  // namespace cvc5

namespace std {

size_t hash<cvc5::ProofRewriteRule>::operator()(
    cvc5::ProofRewriteRule rule) const
{
  return static_cast<size_t>(rule);
}

std::string to_string(cvc5::ProofRewriteRule rule)
{
  return cvc5::toString(rule);
}

}  // namespace std
