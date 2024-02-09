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
 * Implementation of Alf proof rules
 */

#include "proof/alf/alf_proof_rule.h"

#include <iostream>

#include "proof/proof_checker.h"

namespace cvc5::internal {
namespace proof {

const char* AlfRuleToString(AlfRule id)
{
  switch (id)
  {
    case AlfRule::CONG: return "cong";
    case AlfRule::NARY_CONG: return "nary_cong";
    //================================================= Undefined rule
    case AlfRule::UNDEFINED: return "undefined";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, AlfRule id)
{
  out << AlfRuleToString(id);
  return out;
}

AlfRule getAlfRule(Node n)
{
  uint32_t id;
  if (ProofRuleChecker::getUInt32(n, id))
  {
    return static_cast<AlfRule>(id);
  }
  return AlfRule::UNDEFINED;
}

}  // namespace proof
}  // namespace cvc5::internal
