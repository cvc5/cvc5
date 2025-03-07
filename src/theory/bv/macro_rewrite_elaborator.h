/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Methods for elaborating MACRO_BV_* proof rewrites.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__MACRO_REWRITE_ELABORATOR_H
#define CVC5__THEORY__BV__MACRO_REWRITE_ELABORATOR_H

#include "proof/proof.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

/**
 * Methods for elaborating MACRO_BV_* proof rewrites. This class is called
 * during RARE proof reconstruction.
 */
class MacroRewriteElaborator : protected EnvObj
{
 public:
  /** Constructor */
  MacroRewriteElaborator(Env& env);
  ~MacroRewriteElaborator();
  /**
   * Elaborate a rewrite eq that was proven by a macro rewrite rule.
   *
   * @param cdp The proof to add to.
   * @param id The (macro) rewrite id that proved the rewrite.
   * @param eq The rewrite proven.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofFor(CDProof* cdp, ProofRewriteRule id, const Node& eq);
};

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BV__MACRO_REWRITE_ELABORATOR_H */
