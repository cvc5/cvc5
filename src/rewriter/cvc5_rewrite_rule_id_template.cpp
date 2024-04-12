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
 * Generated rewrite proof rules.
 */

#include "base/check.h"
#include "cvc5/cvc5_rewrite_rule_id.h"

namespace cvc5 {

const char* toString(cvc5::RewriteRuleId id)
{
  switch (id)
  {
    case RewriteRuleId::NONE:
      return "NONE";
      // clang-format off
${printer}$
    default : Unreachable();
      // clang-format on
  }
}

std::ostream& operator<<(std::ostream& out, RewriteRuleId id)
{
  out << toString(id);
  return out;
}

}  // namespace cvc5

namespace std {

size_t hash<cvc5::RewriteRuleId>::operator()(cvc5::RewriteRuleId id) const
{
  return static_cast<size_t>(id);
}

std::string to_string(cvc5::RewriteRuleId id) { return cvc5::toString(id); }

}  // namespace std
