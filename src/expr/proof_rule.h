/*********************                                                        */
/*! \file proof_rule.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Proof rule enumeration
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__PROOF_RULE_H
#define CVC4__EXPR__PROOF_RULE_H

#include <iosfwd>

namespace CVC4 {

/**
 * An enumeration for proof rules. This enumeration is analogous to Kind for
 * Node objects. In the documentation below, P:F denotes a ProofNode that
 * proves formula F.
 *
 * Conceptually, the following proof rules form a calculus whose target
 * user is the Node-level theory solvers. This means that the rules below
 * are designed to reason about, among other things, common operations on Node
 * objects like Rewriter::rewrite or Node::substitute. It is intended to be
 * translated or printed in other formats.
 *
 * The following PfRule values include core rules and those categorized by
 * theory, including the theory of equality.
 *
 * The "core rules" include two distinguished rules which have special status:
 * (1) ASSUME, which represents an open leaf in a proof.
 * (2) SCOPE, which closes the scope of assumptions.
 * The core rules additionally correspond to generic operations that are done
 * internally on nodes, e.g. calling Rewriter::rewrite.
 *
 * Rules with prefix MACRO_ are those that can be defined in terms of other
 * rules. These exist for convienience. We provide their definition in the line
 * "Macro:".
 */
enum class PfRule : uint32_t
{
  //================================================= Core rules
  //======================== Assume and Scope
  // ======== Assumption (a leaf)
  // Children: none
  // Arguments: (F)
  // --------------
  // Conclusion: F
  //
  // This rule has special status, in that an application of assume is an
  // open leaf in a proof that is not (yet) justified. An assume leaf is
  // analogous to a free variable in a term, where we say "F is a free
  // assumption in proof P" if it contains an application of F that is not
  // bound by SCOPE (see below).
  ASSUME,
  // ======== Scope (a binder for assumptions)
  // Children: (P:F)
  // Arguments: (F1, ..., Fn)
  // --------------
  // Conclusion: (=> (and F1 ... Fn) F) or (not (and F1 ... Fn)) if F is false
  //
  // This rule has a dual purpose with ASSUME. It is a way to close
  // assumptions in a proof. We require that F1 ... Fn are free assumptions in
  // P and say that F1, ..., Fn are not free in (SCOPE P). In other words, they
  // are bound by this application. For example, the proof node:
  //   (SCOPE (ASSUME F) :args F)
  // has the conclusion (=> F F) and has no free assumptions. More generally, a
  // proof with no free assumptions always concludes a valid formula.
  SCOPE,

  //%%%%%%%%%%%%%  BEGIN SHOULD BE AUTO GENERATED

  //======================== Node operations
  // ======== Substitution
  // Children: (P1:(= x1 t1), ..., Pn:(= xn tn))
  // Arguments: (t)
  // ---------------------------------------------------------------
  // Conclusion: (= t t.substitute(x1,t1). ... .substitute(xn,tn))
  // Notice that the orientation of the premises matters.
  SUBS,
  // ======== Rewrite
  // Children: none
  // Arguments: (t)
  // ----------------------------------------
  // Conclusion: (= t Rewriter::rewrite(t))
  REWRITE,
  // ======== Substitution + rewriting
  // ======== Substitution + Rewriting equality introduction
  //
  // In this rule, we provide a term t and conclude that it is equal to its
  // rewritten form under a (proven) substitution.
  //
  // Children: (P1:(= x1 t1), ..., Pn:(= xn tn))
  // Arguments: (t, id?)
  // ---------------------------------------------------------------
  // Conclusion: (= t t')
  // where
  //   t' is toWitness(Rewriter{id}(toSkolem(t).substitute(x1...xn,t1...tn)))
  //   toSkolem(...) converts terms from witness form to Skolem form,
  //   toWitness(...) converts terms from Skolem form to witness form.
  //
  // Notice that:
  //   toSkolem(t') = Rewriter{id}(toSkolem(t).substitute(x1...xn,t1...tn))
  // In other words, from the point of view of Skolem forms, this rule
  // transforms t to t' by standard substitution + rewriting.
  //
  // The argument id is optional and specifies the identifier of the rewriter to
  // be used (see theory/builtin/proof_checker.h).
  MACRO_SR_EQ_INTRO,
  // ======== Substitution + Rewriting predicate introduction
  //
  // In this rule, we provide a formula F and conclude it, under the condition
  // that it rewrites to true under a proven substitution.
  //
  // Children: (P1:(= x1 t1), ..., Pn:(= xn tn))
  // Arguments: (F, id?)
  // ---------------------------------------------------------------
  // Conclusion: F
  // where
  //   Rewriter{id}(F.substitute(x1...xn,t1...tn)) == true
  //
  // Notice that we apply rewriting on the witness form of F, meaning that this
  // rule may conclude an F whose Skolem form is justified by the definition of
  // its (fresh) Skolem variables. Furthermore, notice that the rewriting and
  // substitution is applied only within the side condition, meaning the
  // rewritten form of the witness form of F does not escape this rule.
  MACRO_SR_PRED_INTRO,
  // ======== Substitution + Rewriting predicate elimination
  //
  // In this rule, if we have proven a formula F, then we may conclude its
  // rewritten form under a proven substitution.
  //
  // Children: (P1:F, P2:(= x1 t1), ..., P_{n+1}:(= xn tn))
  // Arguments: (id?)
  // ----------------------------------------
  // Conclusion: F'
  // where
  //   F' is toWitness(Rewriter{id}(toSkolem(F).substitute(x1...xn,t1...tn))).
  //
  // We rewrite only on the Skolem form of F, similar to MACRO_SR_EQ_INTRO.
  MACRO_SR_PRED_ELIM,
  // ======== Substitution + Rewriting predicate transform
  //
  // In this rule, if we have proven a formula F, then we may provide a formula
  // G and conclude it if F and G are equivalent after rewriting under a proven
  // substitution.
  //
  // Children: (P1:F, P2:(= x1 t1), ..., P_{n+1}:(= xn tn))
  // Arguments: (G, id?)
  // ----------------------------------------
  // Conclusion: G
  // where
  //   Rewriter{id}(F.substitute(x1...xn,t1...tn)) ==
  //   Rewriter{id}(G.substitute(x1...xn,t1...tn))
  //
  // Notice that we apply rewriting on the witness form of F and G, similar to
  // MACRO_SR_PRED_INTRO.
  MACRO_SR_PRED_TRANSFORM,
  // ======== Theory lemma
  // Children: none
  // Arguments: (tid)
  // ---------------------------------------------------------------
  // Conclusion: F
  // where F is a (T-valid) theory lemma generated by theory with TheoryId tid.
  // This is a "coarse-grained" rule that is used as a placeholder if a theory
  // did not provide a proof for a lemma or conflict.
  THEORY_LEMMA,
  // ======== Theory preprocess
  // Children: (F)
  // Arguments: none
  // ---------------------------------------------------------------
  // Conclusion: TheoryEngine::preprocess(F).
  THEORY_PREPROCESS,

  //================================================= Boolean rules
  // ======== Split
  // Children: none
  // Arguments: (F)
  // ---------------------
  // Conclusion: (or F (not F))
  SPLIT,
  // ======== And elimination
  // Children: (P:(and F1 ... Fn))
  // Arguments: (i)
  // ---------------------
  // Conclusion: (Fi)
  AND_ELIM,
  // ======== Not Or elimination
  // Children: (P:(not (or F1 ... Fn)))
  // Arguments: (i)
  // ---------------------
  // Conclusion: (not Fi)
  NOT_OR_ELIM,
  // ======== Implication elimination
  // Children: (P:(=> F1 F2))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or (not F1) F2)
  IMPLIES_ELIM,
  // ======== Not Implication elimination version 1
  // Children: (P:(not (=> F1 F2)))
  // Arguments: ()
  // ---------------------
  // Conclusion: (F1)
  NOT_IMPLIES_ELIM1,
  // ======== Not Implication elimination version 2
  // Children: (P:(not (=> F1 F2)))
  // Arguments: ()
  // ---------------------
  // Conclusion: (not F2)
  NOT_IMPLIES_ELIM2,
  // ======== Equivalence elimination version 1
  // Children: (P:(= F1 F2))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or (not F1) F2)
  EQUIV_ELIM1,
  // ======== Equivalence elimination version 2
  // Children: (P:(= F1 F2))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or F1 (not F2))
  EQUIV_ELIM2,
  // ======== Not Equivalence elimination version 1
  // Children: (P:(not (= F1 F2)))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or F1 F2)
  NOT_EQUIV_ELIM1,
  // ======== Not Equivalence elimination version 2
  // Children: (P:(not (= F1 F2)))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or (not F1) (not F2))
  NOT_EQUIV_ELIM2,
  // ======== XOR elimination version 1
  // Children: (P:(xor F1 F2)))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or F1 F2)
  XOR_ELIM1,
  // ======== XOR elimination version 2
  // Children: (P:(xor F1 F2)))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or (not F1) (not F2))
  XOR_ELIM2,
  // ======== Not XOR elimination version 1
  // Children: (P:(not (xor F1 F2)))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or F1 (not F2))
  NOT_XOR_ELIM1,
  // ======== Not XOR elimination version 2
  // Children: (P:(not (xor F1 F2)))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or (not F1) F2)
  NOT_XOR_ELIM2,
  // ======== ITE elimination version 1
  // Children: (P:(ite C F1 F2))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or (not C) F1)
  ITE_ELIM1,
  // ======== ITE elimination version 2
  // Children: (P:(ite C F1 F2))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or C F2)
  ITE_ELIM2,
  // ======== Not ITE elimination version 1
  // Children: (P:(not (ite C F1 F2)))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or (not C) (not F1))
  NOT_ITE_ELIM1,
  // ======== Not ITE elimination version 1
  // Children: (P:(not (ite C F1 F2)))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or C (not F2))
  NOT_ITE_ELIM2,

  //================================================= Equality rules
  // ======== Reflexive
  // Children: none
  // Arguments: (t)
  // ---------------------
  // Conclusion: (= t t)
  REFL,
  // ======== Symmetric
  // Children: (P:(= t1 t2))
  // Arguments: none
  // -----------------------
  // Conclusion: (= t2 t1)
  SYMM,
  // ======== Transitivity
  // Children: (P1:(= t1 t2), ..., Pn:(= t{n-1} tn))
  // Arguments: none
  // -----------------------
  // Conclusion: (= t1 tn)
  TRANS,
  // ======== Congruence  (subsumed by Substitute?)
  // Children: (P1:(= t1 s1), ..., Pn:(= tn sn))
  // Arguments: (f)
  // ---------------------------------------------
  // Conclusion: (= (f t1 ... tn) (f s1 ... sn))
  CONG,
  // ======== True intro
  // Children: (P:F)
  // Arguments: none
  // ----------------------------------------
  // Conclusion: (= F true)
  TRUE_INTRO,
  // ======== True elim
  // Children: (P:(= F true)
  // Arguments: none
  // ----------------------------------------
  // Conclusion: F
  TRUE_ELIM,
  // ======== False intro
  // Children: (P:(not F))
  // Arguments: none
  // ----------------------------------------
  // Conclusion: (= F false)
  FALSE_INTRO,
  // ======== False elim
  // Children: (P:(= F false)
  // Arguments: none
  // ----------------------------------------
  // Conclusion: (not F)
  FALSE_ELIM,

  //================================================= String rules
  //======================== Core solver
  // ======== Concat eq
  // Children: (P1:(= (str.++ t1 ... tn t) (str.++ t1 ... tn s)))
  // Arguments: (b), indicating if reverse direction
  // ---------------------
  // Conclusion: (= t s)
  //
  // Notice that t or s may be empty, in which case they are implicit in the
  // concatenation above. For example, if
  // P1 concludes (= x (str.++ x z)), then
  // (CONCAT_EQ P1 :args false) concludes (= "" z)
  //
  // Also note that constants are split, such that if
  // P1 concludes (= (str.++ "abc" x) (str.++ "a" y)), then
  // (CONCAT_EQ P1 :args false) concludes (= (str.++ "bc" x) y)
  // This splitting is done only for constants such that Word::splitConstant
  // returns non-null.
  CONCAT_EQ,
  // ======== Concat unify
  // Children: (P1:(= (str.++ t1 t2) (str.++ s1 s2)),
  //            P2:(= (str.len t1) (str.len s1)))
  // Arguments: (b), indicating if reverse direction
  // ---------------------
  // Conclusion: (= t1 s1)
  CONCAT_UNIFY,
  // ======== Concat conflict
  // Children: (P1:(= (str.++ c1 t) (str.++ c2 s)))
  // Arguments: (b), indicating if reverse direction
  // ---------------------
  // Conclusion: false
  // Where c1, c2 are constants such that Word::splitConstant(c1,c2,index,b)
  // is null, in other words, neither is a prefix of the other.
  CONCAT_CONFLICT,
  // ======== Concat split
  // Children: (P1:(= (str.++ t1 t2) (str.++ s1 s2)),
  //            P2:(not (= (str.len t1) (str.len s1))))
  // Arguments: (false)
  // ---------------------
  // Conclusion: (or (= t1 (str.++ s1 r_t)) (= s1 (str.++ t1 r_s)))
  // where
  //   r_t = (witness ((z String)) (= z (suf t1 (str.len s1)))),
  //   r_s = (witness ((z String)) (= z (suf s1 (str.len t1)))).
  //
  // or the reverse form of the above:
  //
  // Children: (P1:(= (str.++ t1 t2) (str.++ s1 s2)),
  //            P2:(not (= (str.len t2) (str.len s2))))
  // Arguments: (true)
  // ---------------------
  // Conclusion: (or (= t2 (str.++ r_t s2)) (= s2 (str.++ r_s t2)))
  // where
  //   r_t = (witness ((z String)) (= z (pre t2 (- (str.len t2) (str.len
  //   s2))))), r_s = (witness ((z String)) (= z (pre s2 (- (str.len s2)
  //   (str.len t2))))).
  //
  // Above, (suf x n) is shorthand for (str.substr x n (- (str.len x) n)) and
  // (pre x n) is shorthand for (str.substr x 0 n).
  CONCAT_SPLIT,
  // ======== Concat constant split
  // Children: (P1:(= (str.++ t1 t2) (str.++ c s2)),
  //            P2:(not (= (str.len t1) 0)))
  // Arguments: (false)
  // ---------------------
  // Conclusion: (= t1 (str.++ c r))
  // where
  //   r = (witness ((z String)) (= z (suf t1 1))).
  //
  // or the reverse form of the above:
  //
  // Children: (P1:(= (str.++ t1 t2) (str.++ s1 c)),
  //            P2:(not (= (str.len t2) 0)))
  // Arguments: (true)
  // ---------------------
  // Conclusion: (= t2 (str.++ r c))
  // where
  //   r = (witness ((z String)) (= z (pre t2 (- (str.len t2) 1)))).
  CONCAT_CSPLIT,
  // ======== Concat length propagate
  // Children: (P1:(= (str.++ t1 t2) (str.++ s1 s2)),
  //            P2:(> (str.len t1) (str.len s1)))
  // Arguments: (false)
  // ---------------------
  // Conclusion: (= t1 (str.++ s1 r_t))
  // where
  //   r_t = (witness ((z String)) (= z (suf t1 (str.len s1))))
  //
  // or the reverse form of the above:
  //
  // Children: (P1:(= (str.++ t1 t2) (str.++ s1 s2)),
  //            P2:(> (str.len t2) (str.len s2)))
  // Arguments: (false)
  // ---------------------
  // Conclusion: (= t2 (str.++ r_t s2))
  // where
  //   r_t = (witness ((z String)) (= z (pre t2 (- (str.len t2) (str.len
  //   s2))))).
  CONCAT_LPROP,
  // ======== Concat constant propagate
  // Children: (P1:(= (str.++ t1 w1 t2) (str.++ w2 s)),
  //            P2:(not (= (str.len t1) 0)))
  // Arguments: (false)
  // ---------------------
  // Conclusion: (= t1 (str.++ w3 r))
  // where
  //   w1, w2, w3, w4 are words,
  //   w3 is (pre w2 p),
  //   w4 is (suf w2 p),
  //   p = Word::overlap((suf w2 1), w1),
  //   r = (witness ((z String)) (= z (suf t1 (str.len w3)))).
  // In other words, w4 is the largest suffix of (suf w2 1) that can contain a
  // prefix of w1; since t1 is non-empty, w3 must therefore be contained in t1.
  //
  // or the reverse form of the above:
  //
  // Children: (P1:(= (str.++ t1 w1 t2) (str.++ s w2)),
  //            P2:(not (= (str.len t2) 0)))
  // Arguments: (true)
  // ---------------------
  // Conclusion: (= t2 (str.++ r w3))
  // where
  //   w1, w2, w3, w4 are words,
  //   w3 is (suf w2 (- (str.len w2) p)),
  //   w4 is (pre w2 (- (str.len w2) p)),
  //   p = Word::roverlap((pre w2 (- (str.len w2) 1)), w1),
  //   r = (witness ((z String)) (= z (pre t2 (- (str.len t2) (str.len w3))))).
  // In other words, w4 is the largest prefix of (pre w2 (- (str.len w2) 1))
  // that can contain a suffix of w1; since t2 is non-empty, w3 must therefore
  // be contained in t2.
  CONCAT_CPROP,
  // ======== Length positive
  // Children: none
  // Arguments: (t)
  // ---------------------
  // Conclusion: (or (and (= (str.len t) 0) (= t "")) (> (str.len t 0)))
  LENGTH_POS,
  // ======== Length non-empty
  // Children: (P1:(not (= t "")))
  // Arguments: none
  // ---------------------
  // Conclusion: (not (= (str.len t) 0))
  LENGTH_NON_EMPTY,
  //======================== Extended functions
  // ======== Contains not equal
  // Children: (P1:(not (str.contains s t)))
  // Arguments: none
  // -------------------
  // Conclusion: (not (= s t))
  CTN_NOT_EQUAL,
  // ======== Reduction
  // Children: none
  // Arguments: (t)
  // ---------------------
  // Conclusion: (and R (= t w))
  // where w = StringsPreprocess::reduce(t, R, ...).
  // In other words, R is the reduction predicate for extended term t, and w is
  //   (witness ((z T)) (= z t))
  // Notice that the free variables of R are w and the free variables of t.
  STRINGS_REDUCTION,
  // ======== Eager Reduction
  // Children: none
  // Arguments: (t, id?)
  // ---------------------
  // Conclusion: R
  // where R = StringsPreprocess::eagerReduce(t, id).
  STRINGS_EAGER_REDUCTION,
  //======================== Regular expressions
  // ======== Regular expression intersection
  // Children: (P:(str.in.re t R1), P:(str.in.re t R2))
  // Arguments: none
  // ---------------------
  // Conclusion: (str.in.re t (re.inter R1 R2)).
  RE_INTER,
  // ======== Regular expression unfold positive
  // Children: (P:(str.in.re t R))
  // Arguments: none
  // ---------------------
  // Conclusion:(RegExpOpr::reduceRegExpPos(t,R)),
  // corresponding to the one-step unfolding of the premise.
  RE_UNFOLD_POS,
  // ======== Regular expression unfold negative
  // Children: (P:(not (str.in.re t R)))
  // Arguments: none
  // ---------------------
  // Conclusion:(RegExpOpr::reduceRegExpNeg(t,R)),
  // corresponding to the one-step unfolding of the premise.
  RE_UNFOLD_NEG,

  //%%%%%%%%%%%%%  BEGIN UNTRUSTWORTHY
  // These allow an untrustworthy conversion from strings::Inference to PfRule
  SIU_BEGIN,

  SIU_I_NORM_S,
  SIU_I_CONST_MERGE,
  SIU_I_CONST_CONFLICT,
  SIU_I_NORM,
  SIU_CARD_SP,
  SIU_CARDINALITY,
  SIU_I_CYCLE_E,
  SIU_I_CYCLE,
  SIU_F_CONST,
  SIU_F_UNIFY,
  SIU_F_ENDPOINT_EMP,
  SIU_F_ENDPOINT_EQ,
  SIU_F_NCTN,
  SIU_N_ENDPOINT_EMP,
  SIU_N_UNIFY,
  SIU_N_ENDPOINT_EQ,
  SIU_N_CONST,
  SIU_INFER_EMP,
  SIU_SSPLIT_CST_PROP,
  SIU_SSPLIT_VAR_PROP,
  SIU_LEN_SPLIT,
  SIU_LEN_SPLIT_EMP,
  SIU_SSPLIT_CST,
  SIU_SSPLIT_VAR,
  SIU_FLOOP,
  SIU_FLOOP_CONFLICT,
  SIU_NORMAL_FORM,
  SIU_N_NCTN,
  SIU_LEN_NORM,
  SIU_DEQ_DISL_EMP_SPLIT,
  SIU_DEQ_DISL_FIRST_CHAR_EQ_SPLIT,
  SIU_DEQ_DISL_FIRST_CHAR_STRING_SPLIT,
  SIU_DEQ_DISL_STRINGS_SPLIT,
  SIU_DEQ_STRINGS_EQ,
  SIU_DEQ_LENS_EQ,
  SIU_DEQ_NORM_EMP,
  SIU_DEQ_LENGTH_SP,
  SIU_CODE_PROXY,
  SIU_CODE_INJ,
  SIU_RE_NF_CONFLICT,
  SIU_RE_UNFOLD_POS,
  SIU_RE_UNFOLD_NEG,
  SIU_RE_INTER_INCLUDE,
  SIU_RE_INTER_CONF,
  SIU_RE_INTER_INFER,
  SIU_RE_DELTA,
  SIU_RE_DELTA_CONF,
  SIU_RE_DERIVE,
  SIU_EXTF,
  SIU_EXTF_N,
  SIU_EXTF_D,
  SIU_EXTF_D_N,
  SIU_EXTF_EQ_REW,
  SIU_CTN_TRANS,
  SIU_CTN_DECOMPOSE,
  SIU_CTN_NEG_EQUAL,
  SIU_CTN_POS,
  SIU_REDUCTION,
  SIU_PREFIX_CONFLICT,

  SIU_END,
  //%%%%%%%%%%%%%  END UNTRUSTWORTHY

  //%%%%%%%%%%%%%  END SHOULD BE AUTO GENERATED

  //================================================= Unknown rule
  UNKNOWN,
};

/**
 * Converts a proof rule to a string. Note: This function is also used in
 * `safe_print()`. Changing this function name or signature will result in
 * `safe_print()` printing "<unsupported>" instead of the proper strings for
 * the enum values.
 *
 * @param id The proof rule
 * @return The name of the proof rule
 */
const char* toString(PfRule id);

/**
 * Writes a proof rule name to a stream.
 *
 * @param out The stream to write to
 * @param id The proof rule to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, PfRule id);

}  // namespace CVC4

#endif /* CVC4__EXPR__PROOF_RULE_H */
