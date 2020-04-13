/*********************                                                        */
/*! \file proof_step.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Proof step enumeration
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__PROOF_STEP_H
#define CVC4__EXPR__PROOF_STEP_H

#include "util/safe_print.h"

namespace CVC4 {

/** Types of proof steps used in the procedure
 */
enum class ProofStep : uint32_t
{
  //================================================= CORE
  // ======== Assumption (a leaf)
  // Children: none
  // Arguments: (F)
  // --------------
  // Conclusion P:F
  ASSUME,
  // ======== Substitution
  // Children: (P:(= x1 t1), ..., P:(= xn tn))
  // Arguments: (t)
  // ---------------------------------------------------------------
  // Conclusion: P:(= t t.substitute(x1,t1). ... .substitute(xn,tn))
  SUBS,
  // ======== Rewrite
  // Children: none
  // Arguments: (t)
  // ----------------------------------------
  // Conclusion: P:(= t Rewriter::rewrite(t))
  REWRITE,
  // ======== Split
  // Children: none
  // Arguments: P:(F)
  // ---------------------
  // Conclusion: (or F (not F))
  SPLIT,

  //================================================= EQUALITY
  // ======== Reflexive
  // Children: none
  // Arguments: (t)
  // ---------------------
  // Conclusion: P:(= t t)
  REFL,
  // ======== Symmetric
  // Children: (P:(= t1 t2))
  // Arguments: none
  // -----------------------
  // Conclusion: P:(= t2 t1)
  SYMM,
  // ======== Transitivity
  // Children: (P:(= t1 t2), ..., P:(= t{n-1} tn))
  // Arguments: none
  // -----------------------
  // Conclusion: P:(= t1 tn)
  TRANS,
  // ======== Congruence  (subsumed by Substitute?)
  // Children: (P:(= t1 s1), ..., P:(= tn sn))
  // Arguments: (f)
  // ---------------------------------------------
  // Conclusion: P:(= (f t1 ... tn) (f s1 ... sn))
  CONG,

  //================================================= THEORY_STRINGS
  //======================== Core solver
  // ======== Concat endpoint unify
  // Children: (P:(= (str.++ r t1) (str.++ r s1)))
  // Arguments: (b), indicating if reverse direction
  // ---------------------
  // Conclusion: P:(= t1 s1)
  CONCAT_ENDP_UNIFY,
  // ======== Normal form unify
  // Children: (P:(= (str.++ t1 t2) (str.++ s1 s2)),
  //            P:(= (str.len t1) (str.len s1)))
  // Arguments: (b), indicating if reverse direction
  // ---------------------
  // Conclusion: P:(= t1 s1)
  CONCAT_UNIFY,
  // ======== Concat split
  // Children: (P:(= (str.++ t1 t2) (str.++ s1 s2)),
  //            P:(not (= (str.len t1) (str.len s1))))
  // Arguments: (b), indicating if reverse direction
  // ---------------------
  // Conclusion: P:(or ... )
  CONCAT_SPLIT,
  // ======== Concat split propagate
  // Children: (P:(= (str.++ t1 t2) (str.++ s1 s2)),
  //            P:(> (str.len t1) (str.len s1)))
  // Arguments: (b), indicating if reverse direction
  // ---------------------
  // Conclusion: P:(= t1 (str.++ s1 ...))
  CONCAT_LPROP,
  // ======== Concat split propagate
  // Children: (P:(= (str.++ t1 w1 t2) (str.++ w2 s1)))
  // Arguments: (b), indicating if reverse direction
  // ---------------------
  // Conclusion: P:(= t1 (str.++ w3 ...)) where w3 ++ w4 = w1 and w4 is the
  // overlap of w1 and w2.
  CONCAT_CPROP,
  //======================== Extended functions
  // ======== Contains not equal
  // Children: (P:(not (str.contains s t)))
  // Arguments: none
  // -------------------
  // Conclusion: P:(not (= s t))
  CTN_NOT_EQUAL,
  // ======== Reduction
  // Children: none
  // Arguments: (t[x])
  // ---------------------
  // Conclusion: P:(and R[x,y] (= t[x] y)) where R is the reduction predicate
  // for extended term t[x].
  REDUCTION,
  //======================== Regular expressions
  // ======== Regular expression intersection
  // Children: (P:(str.in.re t R1), P:(str.in.re t R2))
  // Arguments: none
  // ---------------------
  // Conclusion: P:(str.in.re t (re.inter R1 R2)).
  RE_INTER,
  // ======== Regular expression unfold
  // Children: (P:(str.in.re t R)) or (P:(not (str.in.re t R)))
  // Arguments: none
  // ---------------------
  // Conclusion: P:F, corresponding to the one-step unfolding of the premise.
  RE_UNFOLD,

  //================================================= UNKNOWN
  UNKNOWN,
};

/**
 * Converts an proof step to a string. Note: This function is also used in
 * `safe_print()`. Changing this functions name or signature will result in
 * `safe_print()` printing "<unsupported>" instead of the proper strings for
 * the enum values.
 *
 * @param id The proof step
 * @return The name of the proof step
 */
const char* toString(ProofStep id);

/**
 * Writes an proof step name to a stream.
 *
 * @param out The stream to write to
 * @param id The proof step to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, ProofStep id);

}  // namespace CVC4

#endif /* CVC4__EXPR__PROOF_STEP_H */
