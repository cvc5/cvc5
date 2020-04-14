/*********************                                                        */
/*! \file proof_step.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Proof step enumeration
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__PROOF_STEP_H
#define CVC4__EXPR__PROOF_STEP_H

#include "util/safe_print.h"

namespace CVC4 {

/** 
 * An enumeration for proof steps.
 * This enumeration is analogous to Kind for Node objects.
 */
enum class ProofStep : uint32_t
{
  //================================================= CORE
  // ======== Assumption (a leaf)
  // Children: none
  // Arguments: (F)
  // --------------
  // Conclusion P:F
  ASSUME,

  //================================================= UNKNOWN
  UNKNOWN,
};

/**
 * Converts an proof step to a string. Note: This function is also used in
 * `safe_print()`. Changing this functions name or signature will result in
 * `safe_print()` printing "<unsupported>" instead of the proper strings for
 * the enum values.
 *
 * @param id The proof step
 * @return The name of the proof step
 */
const char* toString(ProofStep id);

/**
 * Writes an proof step name to a stream.
 *
 * @param out The stream to write to
 * @param id The proof step to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, ProofStep id);

}  // namespace CVC4

#endif /* CVC4__EXPR__PROOF_STEP_H */
