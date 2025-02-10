/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Definition of ProofRule::ACI_NORM
 */

#include "cvc5_private.h"

#ifndef CVC5__EXPR__ACI_NORM__H
#define CVC5__EXPR__ACI_NORM__H

#include <map>
#include <vector>

#include "expr/node.h"

namespace cvc5::internal {
namespace expr {

/**
 * Get the null terminator for kind k and type node tn.
 *
 * Examples of null terminators:
 *   false for (OR, bool)
 *   true for (AND, bool)
 *   (as seq.empty (Seq Int)) for (STRING_CONCAT, (Seq Int)
 *   #x0 for (BITVECTOR_OR, (_ BitVec 4))
 */
Node getNullTerminator(Kind k, TypeNode tn);

/**
 * @param k A kind
 * @return true if k is associative, commutative and idempotent.
 */
bool isAssocCommIdem(Kind k);
/**
 * @param k A kind
 * @return true if k is associative.
 */
bool isAssoc(Kind k);
/**
 * Get the normal form of a that takes into account associativity,
 * commutativity, and idempotency if applicable.
 * This is used by ProofRule::NORM.
 *
 * @param a The term.
 * @return its normal form.
 */
Node getACINormalForm(Node a);
/**
 * Return true if a and b can be shown equivalent by computing normal forms as
 * above.
 *
 * @param a The first term
 * @param b The second term
 * @return true if a and b were successfully shown to be equal.
 */
bool isACINorm(Node a, Node b);

}  // namespace expr
}  // namespace cvc5::internal

#endif /* CVC5__EXPR__NARY_TERM_UTIL__H */
