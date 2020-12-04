#include "cvc4_private.h"

#include <iostream>

namespace CVC4 {
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
  SCOPE
};
}
