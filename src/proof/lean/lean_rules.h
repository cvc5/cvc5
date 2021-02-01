#include <iostream>

#include "cvc4_private.h"

namespace CVC4 {
namespace proof {
enum class LeanRule : uint32_t
{
  // in what format should I put these lean rules
  // all the lean rules
  R0,  // describe it
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
