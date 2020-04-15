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
 * The "core rules" include ASSUME, which represents an open leaf in a proof.
 * The core rules additionally correspond to generic operations that are done
 * internally on nodes, e.g. calling Rewriter::rewrite.
 */
enum class PfRule : uint32_t
{
  //================================================= Core rules
  // ======== Assumption (a leaf)
  // Children: none
  // Arguments: (F)
  // --------------
  // Conclusion F
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

  //================================================= Equality rules
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

  //================================================= String rules
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
