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
 * Enumeration of Alf specific proof rules.  These are mostly variants of
 * standard cvc5 rules that are slight adapted to the limits of Alf.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__ALF__ALF_PROOF_RULE_H
#define CVC5__PROOF__ALF__ALF_PROOF_RULE_H

#include <iostream>

#include "expr/node.h"

namespace cvc5::internal {
namespace proof {

/**
 * Custom rules that vary from the internal signature of cvc5.
 * For details, see signatures defined in proofs/alf/Cvc5.smt3.
 */
enum class AlfRule : uint32_t
{
  // congruence
  CONG,
  // n-ary congruence
  NARY_CONG,
  // Used in case that a step in the proof rule could not be translated.
  UNDEFINED
};

/**
 * Converts an ALF proof rule to a string.
 *
 * @param id The ALF proof rule
 * @return The name of the ALF proof rule
 */
const char* AlfRuleToString(AlfRule id);

/**
 * Writes an ALF proof rule name to a stream.
 *
 * @param out The stream to write to
 * @param id The ALF proof rule to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, AlfRule id);

/** Convert a node holding an id to the corresponding AlfRule */
AlfRule getAlfRule(Node n);

}  // namespace proof
}  // namespace cvc5::internal

#endif /* CVC5__PROOF__ALF__ALF_PROOF_RULE_H */
