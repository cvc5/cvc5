/******************************************************************************
 * Top contributors (to current version):
 *   Hanna Lachnitt, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Algorithms used by the Alethe post processor
 */

#ifndef CVC5__PROOF__ALETHE__ALETHE_PROOF_PROCESSOR_ALGORITHM_H
#define CVC5__PROOF__ALETHE__ALETHE_PROOF_PROCESSOR_ALGORITHM_H

#include "proof/proof_node_manager.h"

namespace cvc5::internal {

namespace proof {

/** Transforms a term by applying associativity and idempotency into its ac
 * normal form.
 *
 * @param cache A mapping between subterms of the input term and their ac normal
 * form. Should be empty in the beginning.
 * @param term The term that should be transformed.
 * @return The term in ac normal form.
 */
Node applyAcSimp(std::map<Node, Node>& cache, Node term);

}  // namespace proof
}  // namespace cvc5::internal

#endif
