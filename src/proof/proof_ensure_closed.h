/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Debug checks for ensuring proofs are closed.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__PROOF_ENSURE_CLOSED_H
#define CVC5__PROOF__PROOF_ENSURE_CLOSED_H

#include "expr/node.h"

namespace cvc5::internal {

class Options;
class ProofGenerator;
class ProofNode;

/**
 * Debug check closed on Trace c. Context ctx is string for debugging.
 * This method throws an assertion failure if pg cannot provide a closed
 * proof for fact proven. This is checked only if --proof-check=eager
 * is enabled or the Trace c is enabled.
 *
 * @param reqGen Whether we consider a null generator to be a failure.
 */
void pfgEnsureClosed(const Options& opts,
                     Node proven,
                     ProofGenerator* pg,
                     const char* c,
                     const char* ctx,
                     bool reqGen = true);

/**
 * Debug check closed with Trace c. Context ctx is string for debugging and
 * assumps is the set of allowed open assertions. This method throws an
 * assertion failure if pg cannot provide a proof for fact proven whose
 * free assumptions are contained in assumps.
 *
 * @param reqGen Whether we consider a null generator to be a failure.
 */
void pfgEnsureClosedWrt(const Options& opts,
                        Node proven,
                        ProofGenerator* pg,
                        const std::vector<Node>& assumps,
                        const char* c,
                        const char* ctx,
                        bool reqGen = true);

/**
 * Debug check closed with Trace c, proof node versions. This gives an
 * assertion failure if pn is not closed. Detailed information is printed
 * on trace c. Context ctx is a string used for debugging.
 */
void pfnEnsureClosed(const Options& opts,
                     ProofNode* pn,
                     const char* c,
                     const char* ctx);
/**
 * Same as above, but throws an assertion failure only if the free assumptions
 * of pn are not contained in assumps.
 */
void pfnEnsureClosedWrt(const Options& opts,
                        ProofNode* pn,
                        const std::vector<Node>& assumps,
                        const char* c,
                        const char* ctx);
}  // namespace cvc5::internal

#endif /* CVC5__PROOF__PROOF_ENSURE_CLOSED_H */
