/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
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
#include "theory/strings/macro_rewrite_elaborator.h"

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
  bool prove(CDProof* cdp, Node a, Node b, TheoryRewriteMode tmode);
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
  bool postProve(CDProof* cdp, Node a, Node b, TheoryRewriteMode tmode);
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
   * ProofRewriteRule::MACRO__BOOL_EQ_CONST_EQ.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by ProofRewriteRule::MACRO__BOOL_EQ_CONST_EQ.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofMacroBoolEqConstEq(CDProof* cdp, const Node& eq);
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
   * The variable x is eliminated by introducing a guard (not (= x t)), where
   * t is a term that falsifies all literals containing x, and then applying
   * ProofRewriteRule::QUANT_VAR_ELIM_EQ. The proof does not introduce
   * assumptions, since the quantified formula may contain free variables.
   *
   * Below, RCONS denotes a trusted step with id
   * TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, which is later justified by
   * RARE reconstruction, and QUANT_MINISCOPE_AND, QUANT_MINISCOPE_OR,
   * QUANT_VAR_ELIM_EQ and QUANT_MERGE_PRENEX denote ProofRule::THEORY_REWRITE
   * steps for the corresponding ProofRewriteRule.
   *
   * Single variable case. Here eq is (= Q0 false), where Q0 is
   * (forall ((x T)) (or L1 ... Lk)), whose body is just L1 if k = 1. If k > 1,
   * a proof P_norm of (= Q0 Q) is first built by congruence over RCONS steps,
   * where Q is (forall ((x T)) F), F is (=> (and N1 ... Nk) false), and each
   * Ni is (not Li) normalized to a bound or disequality on x. If k = 1, Q is
   * Q0 and F is L1. With g := (= x t), I := F{x->t}, and
   *
   *   C  := (and (not g) g)        D1 := (or (not g) F)    D2 := (or g F)
   *   Q1 := (forall ((x T)) D1)    Q2 := (forall ((x T)) D2)
   *   Q' := (forall ((x T)) (and D1 D2))
   *   A  := (and Q1 Q2)            A' := (and false Q2)
   *
   * the proof of (= Q false) is
   *
   *     P1        P2        P3         P4
   *  --------  --------  --------  ------------
   *  (= Q Q')  (= Q' A)  (= A A')  (= A' false)
   *  -------------------------------------------- TRANS
   *                  (= Q false)
   *
   * which, if k > 1, is combined with P_norm via TRANS to conclude eq. The
   * subproofs are
   *
   *  P1:
   *  ----------- RCONS  ------- REFL
   *  (= C false)        (= F F)
   *  -------------------------- NARY_CONG  ------------------ ACI_NORM
   *  (= (or C F) (or false F))             (= (or false F) F)
   *  -------------------------------------------------------- TRANS
   *               (= (or C F) F)
   *             ---------------- SYMM  ------------------------ RCONS
   *              (= F (or C F))        (= (or C F) (and D1 D2))
   *             ----------------------------------------------- TRANS
   *                            (= F (and D1 D2))
   *                           ------------------- CONG
   *                                (= Q Q')
   *
   *  P2: -------- QUANT_MINISCOPE_AND      P4: ------------ ABSORB
   *      (= Q' A)                              (= A' false)
   *
   *  P3:                           P_false
   *  -------- QUANT_VAR_ELIM_EQ  -----------
   *  (= Q1 I)                    (= I false)
   *  --------------------------------------- TRANS  --------- REFL
   *                (= Q1 false)                     (= Q2 Q2)
   *  -------------------------------------------------------- NARY_CONG
   *                          (= A A')
   *
   * where P_false is a single RCONS step if k = 1. Otherwise I is (=> N false)
   * with N := (and N1{x->t} ... Nk{x->t}), and P_false is
   *
   *   P_N1 ... P_Nk
   *  --------------- AND_INTRO
   *         N
   *  --------------- TRUE_INTRO  --------------- REFL
   *    (= N true)                (= false false)
   *  ------------------------------------------- CONG  ------------- EVALUATE
   *                (= I IMP)                           (= IMP false)
   *  ----------------------------------------------------------------- TRANS
   *                             (= I false)
   *
   * where IMP := (=> true false), and each P_Ni proves Ni{x->t} from RCONS
   * steps on the ite structure of t, combined via proveTransIneq and
   * proveIneqWeaken.
   *
   * Multiple variable case. Here eq is (= L R) with L := (forall Z G) and
   * R := (forall Y K), where x is the first variable of Z not in Y, K is the
   * disjunction of the literals of G kept in R (false if none), and E is the
   * disjunction of the remaining literals of G. With H := (forall ((x T)) G),
   * the proof of (= H K) is
   *
   *     M1        M2         M3         M4
   *  --------  ---------  ---------  --------
   *  (= H H1)  (= H1 EK)  (= EK FK)  (= FK K)
   *  ---------------------------------------- TRANS
   *                  (= H K)
   *
   * where H1 := (forall ((x T)) (or E K)), HE := (forall ((x T)) E),
   * EK := (or HE K), FK := (or false K), and
   *
   *  M1: -------------- ACI_NORM     M3:   P_base
   *      (= G (or E K))                 ------------  ------- REFL
   *      -------------- CONG            (= HE false)  (= K K)
   *         (= H H1)                    --------------------- NARY_CONG
   *                                           (= EK FK)
   *
   *  M2: --------- QUANT_MINISCOPE_OR  M4: -------- RCONS
   *      (= H1 EK)                         (= FK K)
   *
   * Here P_base is the proof of (= HE false) given by the single variable
   * case. The variables Y are free in HE, hence that proof must not introduce
   * assumptions. M1 is omitted if G is (or E K). If no literal of G is kept,
   * then K is false, E is G and HE is H, so P_base already proves (= H K) and
   * the TRANS step above is not recorded, since CDProof does not overwrite an
   * existing proof. Finally, with HY := (forall Y H) and H' the result of
   * merging the quantifier prefixes of HY, eq is concluded by
   *
   *                                 --------- QUANT_MERGE_PRENEX
   *                                 (= HY H')       (= H K)
   *  -------- QUANT_VAR_REORDERING  --------- SYMM  --------- CONG
   *  (= L H')                       (= H' HY)       (= HY R)
   *  -------------------------------------------------------- TRANS
   *                          (= L R)
   *
   * where the QUANT_VAR_REORDERING step is omitted if L is H'.
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
   * ProofRewriteRule::MACRO_LAMBDA_CAPTURE_AVOID or
   * ProofRewriteRule::MACRO_QUANT_ELIM_SHADOW. This rule uses the conversion
   * utility to generate small step rewrites to justify the overall rewrite.
   *
   * @param cdp The proof to add to.
   * @param eq The rewrite proven by
   * ProofRewriteRule::MACRO_LAMBDA_CAPTURE_AVOID or
   * ProofRewriteRule::MACRO_QUANT_ELIM_SHADOW.
   * @return true if added a closed proof of eq to cdp.
   */
  bool ensureProofMacroElimShadow(CDProof* cdp, const Node& eq);
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
  /** Prove symmetry of equality eq, in particular eq[1] == eq[0]. */
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
   * Try a specific theory rewrite to prove eq. Return true if successful.
   */
  bool doTheoryRewrite(CDProof* cdp, const Node& eq, ProofRewriteRule r);
  /**
   * Counts number of proof nodes for each kind of THEORY_REWRITE that were
   * expanded in macro elimination by this class.
   */
  HistogramStat<ProofRewriteRule> d_theoryRewriteMacroExpand;
  /** The BV rewrite elaborator */
  theory::bv::MacroRewriteElaborator d_bvRewElab;
  /** The strings rewrite elaborator */
  theory::strings::MacroRewriteElaborator d_strRewElab;
};

}  // namespace rewriter
}  // namespace cvc5::internal

#endif
