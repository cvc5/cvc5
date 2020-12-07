/*********************                                                        */
/*! \file proof_ensure_closed.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Debug checks for ensuring proofs are closed
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__PROOF_ENSURE_CLOSED_H
#define CVC4__EXPR__PROOF_ENSURE_CLOSED_H

#include "expr/node.h"
#include "expr/proof_generator.h"
#include "expr/proof_node.h"

namespace CVC4 {

/**
 * Debug check closed on Trace c. Context ctx is string for debugging.
 * This method throws an assertion failure if pg cannot provide a closed
 * proof for fact proven. This is checked only if --proof-new-eager-checking
 * is enabled or the Trace c is enabled.
 *
 * @param reqGen Whether we consider a null generator to be a failure.
 */
void pfgEnsureClosed(Node proven,
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
void pfgEnsureClosedWrt(Node proven,
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
void pfnEnsureClosed(ProofNode* pn, const char* c, const char* ctx);
/**
 * Same as above, but throws an assertion failure only if the free assumptions
 * of pn are not contained in assumps.
 */
void pfnEnsureClosedWrt(ProofNode* pn,
                        const std::vector<Node>& assumps,
                        const char* c,
                        const char* ctx);
}  // namespace CVC4

#endif /* CVC4__EXPR__PROOF_ENSURE_CLOSED_H */
