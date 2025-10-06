/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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

 private:
  /**
   * Elaborate a rewrite eq that was proven by a simplify rule.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofForSimplify(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by a concat merge rule.
   *
   * @param cdp The proof to add to.
   * @param id The (macro) rewrite id that proved the rewrite.
   * @param eq The rewrite proven.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofForConcatMerge(CDProof* cdp,
                                 ProofRewriteRule id,
                                 const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by MACRO_BV_EXTRACT_CONCAT.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofForExtractConcat(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by MACRO_BV_MULT_SLT_MULT.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofForMultSltMult(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * MACRO_BV_AND_OR_XOR_CONCAT_PULLUP.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofForAndOrXorConcatPullup(CDProof* cdp, const Node& eq);
  /**
   * Prove congruence for left hand side term n.
   * If n is a term of the form (f t1 ... tn), this proves
   *  (= (f t1 ... sn) (f s1 .... sn))
   * where si is different from ti iff premises[i] is the equality (= ti si).
   * Note that we permit providing null premises[i] in which case si is ti
   * and we prove (= ti ti) by REFL. For example, given
   *   n = (f b a c) and premises = { null, a=b, null }
   * we prove:
   *   ----- REFL        ---- REFL
   *   b = b      a = b  c = c
   *   ------------------------ CONG
   *   (f b a c) = (f b b c)
   */
  Node proveCong(CDProof* cdp,
                 const Node& n,
                 const std::vector<Node>& premises);
};

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BV__MACRO_REWRITE_ELABORATOR_H */
