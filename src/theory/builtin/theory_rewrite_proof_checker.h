/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Builtin proof checker utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BUILTIN__PROOF_CHECKER_H
#define CVC5__THEORY__BUILTIN__PROOF_CHECKER_H

#include "expr/node.h"
#include <cvc5/cvc5_proof_id.h>

namespace cvc5::internal {
namespace theory {
namespace builtin {

/** A checker for builtin proofs */
class TheoryRewriteProofChecker
{
 public:
  /** Constructor. */
  TheoryRewriteProofChecker(NodeManager* nm);
 private:
  /** Pointer to the node manager */
  NodeManager* d_nm;
};

}  // namespace builtin
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BUILTIN__PROOF_CHECKER_H */
