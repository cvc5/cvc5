/*********************                                                        */
/*! \file lean_rules.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Scott Viteri
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for printing Lean proof nodes
 **/

#include "cvc5_private.h"

#ifndef CVC4__PROOF_LEAN_RULES_H
#define CVC4__PROOF_LEAN_RULES_H

#include <iostream>

namespace cvc5 {
namespace proof {
enum class LeanRule : uint32_t
{
  R0,
  R1,
  SMTCONG,
  SMTREFL,
  SMTSYMM,
  SMTSYMM_NEG,
  TRUST,
  ASSUME,
  SCOPE,
  UNKNOWN
};
}
}  // namespace cvc5

#endif /* CVC4__PROOF_LEAN_RULES_H */
