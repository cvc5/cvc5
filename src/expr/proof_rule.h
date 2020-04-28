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
  // Children: (P1:(= x1 t1), ..., Pn:(= xn tn))
  // Arguments: (t)
  // ---------------------------------------------------------------
  // Conclusion:
  //  (= t Rewriter::rewrite(t.substitute(x1,t1). ... .substitute(xn,tn)))
  // Macro: (REWRITE (SUBS P1 ... Pn :args t))
  SUBS_REWRITE,

  //================================================= Boolean rules
  // ======== Split
  // Children: none
  // Arguments: (F)
  // ---------------------
  // Conclusion: (or F (not F))
  SPLIT,

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
  // ======== Equality by substitution + rewriting
  // Children: (P1:(= x1 t1), ..., Pn:(= xn tn))
  // Arguments: (t,s)
  // -------------------
  // Conclusion: (= t s)
  // Macro: (TRANS (SUBS_REWRITE P1 ... Pn :args t)
  //               (SYMM (SUBS_REWRITE P1 ... Pn :args s)))
  // In other words, t and s can be show equal by substitution + rewriting.
  MACRO_EQ_SUBS_REWRITE,
  // ======== Rewrite predicate
  // Children: (P:F)
  // Arguments: none
  // ----------------------------------------
  // Conclusion: Rewriter::rewrite(F)
  // Macro: (TRUE_ELIM (TRANS (SYMM (REWRITE P)) (TRUE_INTRO P)))
  MACRO_REWRITE_PRED,

  //================================================= String rules
  //======================== Core solver
  // ======== Concat endpoint unify
  // Children: (P1:(= (str.++ r t1) (str.++ r s1)))
  // Arguments: (b), indicating if reverse direction
  // ---------------------
  // Conclusion: (= t1 s1)
  CONCAT_ENDP_UNIFY,
  // ======== Normal form unify
  // Children: (P1:(= (str.++ t1 t2) (str.++ s1 s2)),
  //            P2:(= (str.len t1) (str.len s1)))
  // Arguments: (b), indicating if reverse direction
  // ---------------------
  // Conclusion: (= t1 s1)
  CONCAT_UNIFY,
  // ======== Concat split
  // Children: (P1:(= (str.++ t1 t2) (str.++ s1 s2)),
  //            P2:(not (= (str.len t1) (str.len s1))))
  // Arguments: (b), indicating if reverse direction
  // ---------------------
  // Conclusion: (or ... )
  CONCAT_SPLIT,
  // ======== Concat split propagate
  // Children: (P1:(= (str.++ t1 t2) (str.++ s1 s2)),
  //            P2:(> (str.len t1) (str.len s1)))
  // Arguments: (b), indicating if reverse direction
  // ---------------------
  // Conclusion: (= t1 (str.++ s1 ...))
  CONCAT_LPROP,
  // ======== Concat split propagate
  // Children: (P1:(= (str.++ t1 w1 t2) (str.++ w2 s1)))
  // Arguments: (b), indicating if reverse direction
  // ---------------------
  // Conclusion: (= t1 (str.++ w3 ...)) where w3 ++ w4 = w1 and w4 is the
  // overlap of w1 and w2.
  CONCAT_CPROP,
  //======================== Extended functions
  // ======== Contains not equal
  // Children: (P1:(not (str.contains s t)))
  // Arguments: none
  // -------------------
  // Conclusion: (not (= s t))
  CTN_NOT_EQUAL,
  // ======== Reduction
  // Children: none
  // Arguments: (t[x])
  // ---------------------
  // Conclusion: (and R[x,y] (= t[x] y)) where R is the reduction predicate
  // for extended term t[x].
  REDUCTION,
  //======================== Regular expressions
  // ======== Regular expression intersection
  // Children: (P:(str.in.re t R1), P:(str.in.re t R2))
  // Arguments: none
  // ---------------------
  // Conclusion: (str.in.re t (re.inter R1 R2)).
  RE_INTER,
  // ======== Regular expression unfold
  // Children: (P:(str.in.re t R)) or (P:(not (str.in.re t R)))
  // Arguments: none
  // ---------------------
  // Conclusion:F, corresponding to the one-step unfolding of the premise.
  RE_UNFOLD,

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
