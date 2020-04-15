/*********************                                                        */
/*! \file proof_rule.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Proof rule enumeration
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__PROOF_RULE_H
#define CVC4__EXPR__PROOF_RULE_H

#include <iosfwd>

namespace CVC4 {

/**
 * An enumeration for proof rules. This enumeration is analogous to Kind for
 * Node objects. In the documentation below, P:F denotes a ProofNode that
 * proves formula F.
 *
 * Conceptually, the following proof rules form a calculus whose target
 * user is the Node-level theory solvers. This means that the rules below
 * are designed to reason about, among other things, common operations on Node
 * objects like Rewriter::rewrite or Node::substitute. It is intended to be
 * translated or printed in other formats.
 *
 * The following PfRule values include core rules and those categorized by
 * theory, including the theory of equality.
 *
 * The "core rules" include ASSUME, which represents an open leaf in a proof.
 * The core rules additionally correspond to generic operations that are done
 * internally on nodes, e.g. calling Rewriter::rewrite.
 */
enum class PfRule : uint32_t
{
  //================================================= Core rules
  // ======== Assumption (a leaf)
  // Children: none
  // Arguments: (F)
  // --------------
  // Conclusion F
  ASSUME,

  //================================================= Unknown rule
  UNKNOWN,
};

/**
 * Converts a proof rule to a string. Note: This function is also used in
 * `safe_print()`. Changing this function name or signature will result in
 * `safe_print()` printing "<unsupported>" instead of the proper strings for
 * the enum values.
 *
 * @param id The proof rule
 * @return The name of the proof rule
 */
const char* toString(PfRule id);

/**
 * Writes a proof rule name to a stream.
 *
 * @param out The stream to write to
 * @param id The proof rule to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, PfRule id);

}  // namespace CVC4

#endif /* CVC4__EXPR__PROOF_RULE_H */
