/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Methods for elaborating MACRO_STR_* and related string proof rewrites.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__MACRO_REWRITE_ELABORATOR_H
#define CVC5__THEORY__STRINGS__MACRO_REWRITE_ELABORATOR_H

#include <vector>

#include "proof/proof.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

/**
 * Methods for elaborating string-specific macro proof rewrites. This class is
 * called during RARE proof reconstruction.
 */
class MacroRewriteElaborator : protected EnvObj
{
 public:
  /** Constructor */
  MacroRewriteElaborator(Env& env);
  ~MacroRewriteElaborator();
  /**
   * Elaborate a rewrite eq that was proven by a string-related macro rewrite
   * rule.
   *
   * @param cdp The proof to add to.
   * @param id The (macro) rewrite id that proved the rewrite.
   * @param eq The rewrite proven.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofFor(CDProof* cdp, ProofRewriteRule id, const Node& eq);

 private:
  bool ensureProofForArithStringPredEntail(CDProof* cdp, const Node& eq);
  bool ensureProofForReInterUnionInclusion(CDProof* cdp, const Node& eq);
  bool ensureProofForReInterUnionConstElim(CDProof* cdp, const Node& eq);
  bool ensureProofForSubstrStripSymLength(CDProof* cdp, const Node& eq);
  bool ensureProofForStrEqLenUnifyPrefix(CDProof* cdp, const Node& eq);
  bool ensureProofForStrEqLenUnify(CDProof* cdp, const Node& eq);
  bool ensureProofForOverlap(ProofRewriteRule id,
                             CDProof* cdp,
                             const Node& eq);
  bool ensureProofForStrComponentCtn(CDProof* cdp, const Node& eq);
  bool ensureProofForStrConstNCtnConcat(CDProof* cdp, const Node& eq);
  bool ensureProofForStrInReInclusion(CDProof* cdp, const Node& eq);
  void ensureProofForEncodeTransform(CDProof* cdp,
                                     const Node& eq,
                                     const Node& eqi);
  bool ensureProofForArithPolyNormRel(CDProof* cdp, const Node& eq);
  Node proveGeneralReMembership(CDProof* cdp, const Node& n);
  Node proveSymm(CDProof* cdp, const Node& eq);
  Node proveCong(CDProof* cdp,
                 const Node& n,
                 const std::vector<Node>& premises);
  Node proveDualImplication(CDProof* cdp,
                            const Node& impl,
                            const Node& implRev);
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__MACRO_REWRITE_ELABORATOR_H */
