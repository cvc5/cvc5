/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Hans-Joerg Schurr
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for basic (non-DSL-dependent) automatic reconstructing proofs of
 * THEORY_REWRITE steps.
 */

#include "cvc5_private.h"

#ifndef CVC5__REWRITER__BASIC_REWRITE_RCONS_H
#define CVC5__REWRITER__BASIC_REWRITE_RCONS_H

#include <unordered_set>

#include "expr/node.h"
#include "proof/proof.h"
#include "proof/proof_node_manager.h"
#include "smt/env_obj.h"
#include "theory/builtin/proof_checker.h"
#include "theory/bv/macro_rewrite_elaborator.h"
#include "theory/rewriter.h"

namespace cvc5::internal {
namespace rewriter {

/**
 * Mode for if/when to try THEORY_REWRITE.
 */
enum class TheoryRewriteMode
{
  // Attempt to use the theory rewrites based on their TheoryRewriteCtx setting.
  STANDARD,
  // Only resort to theory rewrites after trying RARE rewrites.
  RESORT,
  // Do not try theory rewrites.
  NEVER,
};

/** Print a TheoryRewriteMode to an output stream */
std::ostream& operator<<(std::ostream& os, TheoryRewriteMode tm);

/**
 * The module for basic (non-DSL-dependent) automatic reconstructing proofs of
 * THEORY_REWRITE steps. It handles special cases that are independent
 * of the user-provided DSL rules, including EVALUATE, REFL, BETA_REDUCE.
 */
class BasicRewriteRCons : protected EnvObj
{
 public:
  BasicRewriteRCons(Env& env);
  ~BasicRewriteRCons() {}
  /**
   * Try to prove (= a b), where a ---> b was a theory rewrite from theory
   * tid with the given method. If this method returns true, then a proof
   * of (= a b) was added to cdp.
   * @param cdp The proof to add to.
   * @param a The left hand side of the equality.
   * @param b The left hand side of the equality.
   * @param tmode Determines if/when to try THEORY_REWRITE.
   * @return true if we successfully added a proof of (= a b) to cdp.
   */
  bool prove(CDProof* cdp,
             Node a,
             Node b,
             TheoryRewriteMode tmode);
  /**
   * There are theory rewrites which cannot be expressed in RARE rules. In this
   * case we need to use proof rules which are not written in RARE. It is only
   * used as a last resort method so this is executed only when other rules
   * fail.
   * @param cdp The proof to add to.
   * @param a The left hand side of the equality.
   * @param b The left hand side of the equality.
   * @param tmode Determines if/when to try THEORY_REWRITE.
   * @return true if we successfully added a proof of (= a b) to cdp.
   */
  bool postProve(CDProof* cdp,
                 Node a,
                 Node b,
                 TheoryRewriteMode tmode);
  /**
   * Add to cdp a proof of eq from free asumption eqi, where eqi is the result
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
   * Ensure we have a proof for theory rewrite id of eq in cdp. This typically
   * adds a single THEORY_REWRITE step to cdp. However, for rules with prefix
   * MACRO_, we perform elaboration.
   * @param cdp The proof to add to.
   * @param id The theory rewrite that proves eq.
   * @param eq The conclusion of the theory rewrite.
   */
  void ensureProofForTheoryRewrite(CDProof* cdp,
                                   ProofRewriteRule id,
                                   const Node& eq);

 private:
  /**
   * Try rule r, return true if eq could be proven by r with arguments args.
   * If this method returns true, a proof of eq was added to cdp.
   * If addStep is true, we add the proof to cdp. Otherwise, the caller is
   * responsible for adding the proof.
   */
  bool tryRule(CDProof* cdp,
               Node eq,
               ProofRule r,
               const std::vector<Node>& args,
               bool addStep = true);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_BOOL_NNF_NORM.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by ProofRewriteRule::MACRO_BOOL_NNF_NORM.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofMacroBoolNnfNorm(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_BOOL_BV_INVERT_SOLVE.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_BOOL_BV_INVERT_SOLVE.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofMacroBoolBvInvertSolve(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_ARITH_INT_EQ_CONFLICT or
   * ProofRewriteRule::MACRO_ARITH_INT_GEQ_TIGHTEN.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_ARITH_INT_EQ_CONFLICT or
   * ProofRewriteRule::MACRO_ARITH_INT_GEQ_TIGHTEN.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofMacroArithIntRelation(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_DT_CONS_EQ.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by ProofRewriteRule::MACRO_DT_CONS_EQ.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofMacroDtConsEq(CDProof* cdp, const Node& eq);
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
   * - Find an approximation for e.g. (- t1 t2) based on Noetzli et al CAV 2019,
   *   using ProofRewriteRule::ARITH_STRING_PRED_SAFE_APPROX.
   * - Prove the approximation using ProofRewriteRule::ARITH_STRING_PRED_ENTAIL.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_ARITH_STRING_PRED_ENTAIL.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofMacroArithStringPredEntail(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_RE_INTER_UNION_INCLUSION.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_RE_INTER_UNION_INCLUSION.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofMacroReInterUnionInclusion(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_SUBSTR_STRIP_SYM_LENGTH.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_SUBSTR_STRIP_SYM_LENGTH.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofMacroSubstrStripSymLength(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_STR_EQ_LEN_UNIFY_PREFIX.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_STR_EQ_LEN_UNIFY_PREFIX.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofMacroStrEqLenUnifyPrefix(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_STR_EQ_LEN_UNIFY.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_STR_EQ_LEN_UNIFY.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofMacroStrEqLenUnify(CDProof* cdp, const Node& eq);
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
  bool ensureProofMacroOverlap(ProofRewriteRule id,
                               CDProof* cdp,
                               const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_STR_COMPONENT_CTN.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_STR_COMPONENT_CTN.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofMacroStrComponentCtn(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_STR_CONST_NCTN_CONCAT.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_STR_CONST_NCTN_CONCAT.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofMacroStrConstNCtnConcat(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_STR_IN_RE_INCLUSION.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_STR_IN_RE_INCLUSION.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofMacroStrInReInclusion(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_RE_INTER_UNION_CONST_ELIM.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_RE_INTER_UNION_CONST_ELIM.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofMacroReInterUnionConstElim(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_QUANT_MERGE_PRENEX.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_QUANT_MERGE_PRENEX.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofMacroQuantMergePrenex(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_QUANT_PRENEX.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_QUANT_PRENEX.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofMacroQuantPrenex(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_QUANT_PARTITION_CONNECTED_FV.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_QUANT_PARTITION_CONNECTED_FV.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofMacroQuantPartitionConnectedFv(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_QUANT_VAR_ELIM_EQ.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_QUANT_VAR_ELIM_EQ.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofMacroQuantVarElimEq(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_QUANT_VAR_ELIM_INEQ.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_QUANT_VAR_ELIM_INEQ.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofMacroQuantVarElimIneq(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_QUANT_DT_VAR_EXPAND.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_QUANT_DT_VAR_EXPAND.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofMacroDtVarExpand(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_QUANT_MINISCOPE.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_QUANT_MINISCOPE.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofMacroQuantMiniscope(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_QUANT_REWRITE_BODY.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_QUANT_REWRITE_BODY.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofMacroQuantRewriteBody(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_BV_EQ_SOLVE.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_BV_EQ_SOLVE.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofMacroBvEqSolve(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_LAMBDA_CAPTURE_AVOID.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_LAMBDA_CAPTURE_AVOID.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofMacroLambdaCaptureAvoid(CDProof* cdp, const Node& eq);
  /**
   * Elaborate a rewrite eq that was proven by
   * ProofRewriteRule::MACRO_ARRAYS_NORMALIZE_OP.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_ARRAYS_NORMALIZE_OP.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofMacroArraysNormalizeOp(CDProof* cdp, const Node& eq);
  /**
   * @param cdp The proof to add to.
   * @param eq The rewrite that can be proven by ProofRule::ARITH_POLY_NORM_REL.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofArithPolyNormRel(CDProof* cdp, const Node& eq);
  /**
   * Given a <= b and b <= c as free assumptions, proves a <= c. Adds the
   * necessary proof steps to cdp.
   * @param cdp The proof to add to.
   * @param leq1 The first inequality.
   * @param leq2 The second inequality.
   * @return the proven inequality.
   */
  Node proveTransIneq(CDProof* cdp, const Node& leq1, const Node& leq2);
  /**
   * Given an (non-strict) inequality src as a free assumption, prove
   * strict inequality or disequality tgt.
   * @param cdp The proof to add to.
   * @param src The non-strict inequality.
   * @param tgt The target to prove.
   * @return true if tgt was successfully proven from src.
   */
  bool proveIneqWeaken(CDProof* cdp, const Node& src, const Node& tgt);
  /**
   * Prove that any string term is in a regular expression that characterizes
   * it. Return the proven regular expression. For example, given (str.++ x "A"
   * y), this method returns (str.in_re (str.++ x "A" y) (re.++ Sigma*
   * (str.to_re "A") Sigma*)).
   */
  Node proveGeneralReMembership(CDProof* cdp, const Node& n);
  /**
   * Prove symmetry of equality eq, in particular this proves eq[1] == eq[0]
   * where eq is an equality and adds it to cdp.
   */
  Node proveSymm(CDProof* cdp, const Node& eq);
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
  /**
   * Assuming cdp has proofs of (=> A B) and (=> B A), this ensures we
   * have a proof of (= A B).
   */
  Node proveDualImplication(CDProof* cdp,
                            const Node& impl,
                            const Node& implRev);
  /**
   * Try THEORY_REWRITE with theory::TheoryRewriteCtx ctx.
   */
  bool tryTheoryRewrite(CDProof* cdp,
                        const Node& eq,
                        theory::TheoryRewriteCtx ctx);
  /**
   * Counts number of proof nodes for each kind of THEORY_REWRITE that were
   * expanded in macro elimination by this class.
   */
  HistogramStat<ProofRewriteRule> d_theoryRewriteMacroExpand;
  /** The BV rewrite elaborator */
  theory::bv::MacroRewriteElaborator d_bvRewElab;
};

}  // namespace rewriter
}  // namespace cvc5::internal

#endif
