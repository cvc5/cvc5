#include "cvc4_private.h"

#ifndef CVC4__PROOF_LEAN_RULES_H
#define CVC4__PROOF_LEAN_RULES_H

#include <iostream>

namespace CVC4 {
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
}  // namespace CVC4

#endif /* CVC4__PROOF_LEAN_RULES_H */
