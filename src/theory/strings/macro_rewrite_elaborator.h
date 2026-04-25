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
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_ARITH_STRING_PRED_ENTAIL.
   *
   * This takes an equality of the form (r t1 t2) = c, where r is an arithmetic
   * relation and c is a Boolean constant. This elaboration consists of several
   * steps, roughly in five steps:
   * - Normalize the relation r to >= or =.
   * - Unfold str.len applications in t1 and t2.
   * - Normalize the relation to one comparing with zero, e.g. (- t1 t2) >= 0.
   * - Find an approximation for e.g. (- t1 t2) based on Noetzli et al CAV
   *   2019, using ProofRewriteRule::ARITH_STRING_PRED_SAFE_APPROX.
   * - Prove the approximation using
   *   ProofRewriteRule::ARITH_STRING_PRED_ENTAIL.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_ARITH_STRING_PRED_ENTAIL.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofForArithStringPredEntail(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_RE_INTER_UNION_INCLUSION.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_RE_INTER_UNION_INCLUSION.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofForReInterUnionInclusion(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_RE_INTER_UNION_CONST_ELIM.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_RE_INTER_UNION_CONST_ELIM.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofForReInterUnionConstElim(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_SUBSTR_STRIP_SYM_LENGTH.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_SUBSTR_STRIP_SYM_LENGTH.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofForSubstrStripSymLength(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_STR_EQ_LEN_UNIFY_PREFIX.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_STR_EQ_LEN_UNIFY_PREFIX.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofForStrEqLenUnifyPrefix(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_STR_EQ_LEN_UNIFY.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_STR_EQ_LEN_UNIFY.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofForStrEqLenUnify(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_STR_SPLIT_CTN or
   * ProofRewriteRule::MACRO_STR_STRIP_ENDPOINTS.
   *
   * @param id The macro rule we are expanding.
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_STR_SPLIT_CTN or
   * ProofRewriteRule::MACRO_STR_STRIP_ENDPOINTS.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofForOverlap(ProofRewriteRule id, CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_STR_COMPONENT_CTN.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_STR_COMPONENT_CTN.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofForStrComponentCtn(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_STR_CONST_NCTN_CONCAT.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_STR_CONST_NCTN_CONCAT.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofForStrConstNCtnConcat(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_STR_IN_RE_INCLUSION.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_STR_IN_RE_INCLUSION.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofForStrInReInclusion(CDProof* cdp, const Node& eq);
  /**
   * Add to cdp a proof of eq from free assumption eqi, where eqi is the result
   * of term conversion via RewriteDbNodeConverter.
   *
   * @param cdp The proof to add to.
   * @param eq The original equality.
   * @param eqi The equality after conversion.
   */
  void ensureProofForEncodeTransform(CDProof* cdp,
                                     const Node& eq,
                                     const Node& eqi);
  /**
   * @param cdp The proof to add to.
   * @param eq The rewrite that can be proven by ProofRule::ARITH_POLY_NORM_REL.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofForArithPolyNormRel(CDProof* cdp, const Node& eq);
  /**
   * Prove that any string term is in a regular expression that characterizes
   * it. Return the proven regular expression. For example, given
   * (str.++ x "A" y), this method returns
   * (str.in_re (str.++ x "A" y) (re.++ Sigma* (str.to_re "A") Sigma*)).
   */
  Node proveGeneralReMembership(CDProof* cdp, const Node& n);
  /**
   * Prove symmetry of equality eq, in particular this proves eq[1] == eq[0]
   * where eq is an equality and adds it to cdp.
   */
  Node proveSymm(CDProof* cdp, const Node& eq);
  /**
   * Assuming cdp has proofs of (=> A B) and (=> B A), this ensures we
   * have a proof of (= A B).
   */
  Node proveDualImplication(CDProof* cdp,
                            const Node& impl,
                            const Node& implRev);
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__MACRO_REWRITE_ELABORATOR_H */
