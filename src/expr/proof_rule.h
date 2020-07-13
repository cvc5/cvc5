/*********************                                                        */
/*! \file proof_rule.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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

  //======================== Builtin theory (common node operations)
  // ======== Substitution
  // Children: (P1:F1, ..., Pn:Fn)
  // Arguments: (t, (ids)?)
  // ---------------------------------------------------------------
  // Conclusion: (= t t*sigma{ids}(Fn)*...*sigma{ids}(F1))
  // where sigma{ids}(Fi) are substitutions, which notice are applied in
  // reverse order.
  // Notice that ids is a MethodId identifier, which determines how to convert
  // the formulas F1, ..., Fn into substitutions.
  SUBS,
  // ======== Rewrite
  // Children: none
  // Arguments: (t, (idr)?)
  // ----------------------------------------
  // Conclusion: (= t Rewriter{idr}(t))
  // where idr is a MethodId identifier, which determines the kind of rewriter
  // to apply, e.g. Rewriter::rewrite.
  REWRITE,
  // ======== Substitution + Rewriting equality introduction
  //
  // In this rule, we provide a term t and conclude that it is equal to its
  // rewritten form under a (proven) substitution.
  //
  // Children: (P1:F1, ..., Pn:Fn)
  // Arguments: (t, (ids (idr)?)?)
  // ---------------------------------------------------------------
  // Conclusion: (= t t')
  // where
  //   t' is
  //   Rewriter{idr}(t*sigma{ids}(Fn)*...*sigma{ids}(F1))
  //
  // In other words, from the point of view of Skolem forms, this rule
  // transforms t to t' by standard substitution + rewriting.
  //
  // The argument ids and idr is optional and specify the identifier of the
  // substitution and rewriter respectively to be used. For details, see
  // theory/builtin/proof_checker.h.
  MACRO_SR_EQ_INTRO,
  // ======== Substitution + Rewriting predicate introduction
  //
  // In this rule, we provide a formula F and conclude it, under the condition
  // that it rewrites to true under a proven substitution.
  //
  // Children: (P1:F1, ..., Pn:Fn)
  // Arguments: (F, (ids (idr)?)?)
  // ---------------------------------------------------------------
  // Conclusion: F
  // where
  //   Rewriter{idr}(toWitness(F)*sigma{ids}(Fn)*...*sigma{ids}(F1)) == true
  // where ids and idr are method identifiers.
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
  // Children: (P1:F, P2:F1, ..., P_{n+1}:Fn)
  // Arguments: ((ids (idr)?)?)
  // ----------------------------------------
  // Conclusion: F'
  // where
  //   F' is
  //   Rewriter{idr}(F*sigma{ids}(Fn)*...*sigma{ids}(F1)).
  // where ids and idr are method identifiers.
  //
  // We rewrite only on the Skolem form of F, similar to MACRO_SR_EQ_INTRO.
  MACRO_SR_PRED_ELIM,
  // ======== Substitution + Rewriting predicate transform
  //
  // In this rule, if we have proven a formula F, then we may provide a formula
  // G and conclude it if F and G are equivalent after rewriting under a proven
  // substitution.
  //
  // Children: (P1:F, P2:F1, ..., P_{n+1}:Fn)
  // Arguments: (G, (ids (idr)?)?)
  // ----------------------------------------
  // Conclusion: G
  // where
  //   Rewriter{idr}(toWitness(F)*sigma{ids}(Fn)*...*sigma{ids}(F1)) ==
  //   Rewriter{idr}(toWitness(G)*sigma{ids}(Fn)*...*sigma{ids}(F1))
  //
  // Notice that we apply rewriting on the witness form of F and G, similar to
  // MACRO_SR_PRED_INTRO.
  MACRO_SR_PRED_TRANSFORM,

  //================================================= Processing rules
  // ======== Preprocess
  // Children: none
  // Arguments: (F)
  // ---------------------------------------------------------------
  // Conclusion: F
  // where F is an equality of the form t = t' where t was replaced by t'
  // based on some preprocessing pass, or otherwise F was added as a new
  // assertion by some preprocessing pass.
  PREPROCESS,
  //================================================= Boolean rules
  // ======== Split
  // Children: none
  // Arguments: (F)
  // ---------------------
  // Conclusion: (or F (not F))
  SPLIT,
  // ======== Equality resolution
  // Children: (P1:F1, P2:(= F1 F2))
  // Arguments: none
  // ---------------------
  // Conclusion: (F2)
  // Note this can optionally be seen as a macro for EQUIV_ELIM1+RESOLUTION.
  EQ_RESOLVE,
  // ======== And elimination
  // Children: (P:(and F1 ... Fn))
  // Arguments: (i)
  // ---------------------
  // Conclusion: (Fi)
  AND_ELIM,
  // ======== And introduction
  // Children: (P1:F1 ... Pn:Fn))
  // Arguments: ()
  // ---------------------
  // Conclusion: (and P1 ... Pn)
  AND_INTRO,
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
  // ======== Not ITE elimination version 1
  // Children: (P1:P P2:(not P))
  // Arguments: ()
  // ---------------------
  // Conclusion: (false)
  CONTRA,

  //================================================= De Morgan rules
  // ======== Not And
  // Children: (P:(not (and F1 ... Fn))
  // Arguments: ()
  // ---------------------
  // Conclusion: (or (not F1) ... (not Fn))
  NOT_AND,
  //================================================= CNF rules
  // ======== CNF And Pos
  // Children: ()
  // Arguments: ((and F1 ... Fn), i)
  // ---------------------
  // Conclusion: (or (not (and F1 ... Fn)) Fi)
  CNF_AND_POS,
  // ======== CNF And Neg
  // Children: ()
  // Arguments: ((and F1 ... Fn))
  // ---------------------
  // Conclusion: (or (and F1 ... Fn) (not F1) ... (not Fn))
  CNF_AND_NEG,
  // ======== CNF Or Pos
  // Children: ()
  // Arguments: ((or F1 ... Fn))
  // ---------------------
  // Conclusion: (or (not (or F1 ... Fn)) F1 ... Fn)
  CNF_OR_POS,
  // ======== CNF Or Neg
  // Children: ()
  // Arguments: ((or F1 ... Fn), i)
  // ---------------------
  // Conclusion: (or (or F1 ... Fn) (not Fi))
  CNF_OR_NEG,
  // ======== CNF Implies Pos
  // Children: ()
  // Arguments: ((implies F1 F2))
  // ---------------------
  // Conclusion: (or (not (implies F1 F2)) (not F1) F2)
  CNF_IMPLIES_POS,
  // ======== CNF Implies Neg version 1
  // Children: ()
  // Arguments: ((implies F1 F2))
  // ---------------------
  // Conclusion: (or (implies F1 F2) F1)
  CNF_IMPLIES_NEG1,
  // ======== CNF Implies Neg version 2
  // Children: ()
  // Arguments: ((implies F1 F2))
  // ---------------------
  // Conclusion: (or (implies F1 F2) (not F2))
  CNF_IMPLIES_NEG2,
  // ======== CNF Equiv Pos version 1
  // Children: ()
  // Arguments: ((= F1 F2))
  // ---------------------
  // Conclusion: (or (not (= F1 F2)) (not F1) F2)
  CNF_EQUIV_POS1,
  // ======== CNF Equiv Pos version 2
  // Children: ()
  // Arguments: ((= F1 F2))
  // ---------------------
  // Conclusion: (or (not (= F1 F2)) F1 (not F2))
  CNF_EQUIV_POS2,
  // ======== CNF Equiv Neg version 1
  // Children: ()
  // Arguments: ((= F1 F2))
  // ---------------------
  // Conclusion: (or (= F1 F2) F1 F2)
  CNF_EQUIV_NEG1,
  // ======== CNF Equiv Neg version 2
  // Children: ()
  // Arguments: ((= F1 F2))
  // ---------------------
  // Conclusion: (or (= F1 F2) (not F1) (not F2))
  CNF_EQUIV_NEG2,
  // ======== CNF Xor Pos version 1
  // Children: ()
  // Arguments: ((xor F1 F2))
  // ---------------------
  // Conclusion: (or (not (xor F1 F2)) F1 F2)
  CNF_XOR_POS1,
  // ======== CNF Xor Pos version 2
  // Children: ()
  // Arguments: ((xor F1 F2))
  // ---------------------
  // Conclusion: (or (not (xor F1 F2)) (not F1) (not F2))
  CNF_XOR_POS2,
  // ======== CNF Xor Neg version 1
  // Children: ()
  // Arguments: ((xor F1 F2))
  // ---------------------
  // Conclusion: (or (xor F1 F2) (not F1) F2)
  CNF_XOR_NEG1,
  // ======== CNF Xor Neg version 2
  // Children: ()
  // Arguments: ((xor F1 F2))
  // ---------------------
  // Conclusion: (or (xor F1 F2) F1 (not F2))
  CNF_XOR_NEG2,
  // ======== CNF ITE Pos version 1
  // Children: ()
  // Arguments: ((ite C F1 F2))
  // ---------------------
  // Conclusion: (or (not (ite C F1 F2)) (not C) F1)
  CNF_ITE_POS1,
  // ======== CNF ITE Pos version 2
  // Children: ()
  // Arguments: ((ite C F1 F2))
  // ---------------------
  // Conclusion: (or (not (ite C F1 F2)) C F2)
  CNF_ITE_POS2,
  // ======== CNF ITE Pos version 3
  // Children: ()
  // Arguments: ((ite C F1 F2))
  // ---------------------
  // Conclusion: (or (not (ite C F1 F2)) F1 F2)
  CNF_ITE_POS3,
  // ======== CNF ITE Neg version 1
  // Children: ()
  // Arguments: ((ite C F1 F2))
  // ---------------------
  // Conclusion: (or (ite C F1 F2) (not C) (not F1))
  CNF_ITE_NEG1,
  // ======== CNF ITE Neg version 2
  // Children: ()
  // Arguments: ((ite C F1 F2))
  // ---------------------
  // Conclusion: (or (ite C F1 F2) C (not F2))
  CNF_ITE_NEG2,
  // ======== CNF ITE Neg version 3
  // Children: ()
  // Arguments: ((ite C F1 F2))
  // ---------------------
  // Conclusion: (or (ite C F1 F2) (not F1) (not F2))
  CNF_ITE_NEG3,

  //================================================= Equality rules
  // ======== Reflexive
  // Children: none
  // Arguments: (t)
  // ---------------------
  // Conclusion: (= t t)
  REFL,
  // ======== Symmetric
  // Children: (P:(= t1 t2)) or (P:(not (= t1 t2)))
  // Arguments: none
  // -----------------------
  // Conclusion: (= t2 t1) or (not (= t2 t1))
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

  //================================================= Quantifiers rules
  // ======== Witness intro
  // Children: (P:F[t])
  // Arguments: (t)
  // ----------------------------------------
  // Conclusion: (= t (witness ((x T)) F[x]))
  // where x is a BOUND_VARIABLE unique to the pair F,t.
  WITNESS_INTRO,
  // ======== Exists intro
  // Children: (P:F[t])
  // Arguments: (t)
  // ----------------------------------------
  // Conclusion: (exists ((x T)) F[x])
  // where x is a BOUND_VARIABLE unique to the pair F,t.
  EXISTS_INTRO,
  // ======== Skolemize
  // Children: (P:(exists ((x1 T1) ... (xn Tn)) F))
  // Arguments: none
  // ----------------------------------------
  // Conclusion: F*sigma
  // sigma maps x1 ... xn to their representative skolems obtained by
  // SkolemManager::mkSkolemize, returned in the skolems argument of that
  // method.
  SKOLEMIZE,
  // ======== Instantiate
  // Children: (P:(forall ((x1 T1) ... (xn Tn)) F))
  // Arguments: (t1 ... tn)
  // ----------------------------------------
  // Conclusion: F*sigma
  // sigma maps x1 ... xn to t1 ... tn.
  INSTANTIATE,

  // ======== Adding Inequalities
  // Note: an ArithLiteral is a term of the form (>< poly const)
  // where
  //   >< is >=, >, ==, <, <=, or not(== ...).
  //   poly is a polynomial
  //   const is a rational constant

  // Children: (P1:l1, ..., Pn:ln)
  //           where each li is an ArithLiteral
  //           not(= ...) is dis-allowed!
  //
  // Arguments: (k1, ..., kn), non-zero reals
  // ---------------------
  // Conclusion: (>< (* k t1) (* k t2))
  //    where >< is the fusion of the combination of the ><i, (flipping each it
  //    its ki is negative). >< is always one of <, <=
  //    NB: this implies that lower bounds must have negative ki,
  //                      and upper bounds must have positive ki.
  //    t1 is the sum of the polynomials.
  //    t2 is the sum of the constants.
  ARITH_SCALE_SUM_UPPER_BOUNDS,

  // ======== Tightening Strict Integer Upper Bounds
  // Children: (P:(< i c))
  //         where i has integer type.
  // Arguments: none
  // ---------------------
  // Conclusion: (<= i greatestIntLessThan(c)})
  INT_TIGHT_UB,

  // ======== Tightening Strict Integer Lower Bounds
  // Children: (P:(> i c))
  //         where i has integer type.
  // Arguments: none
  // ---------------------
  // Conclusion: (>= i leastIntGreaterThan(c)})
  INT_TIGHT_LB,

  // ======== Trichotomy of the reals
  // Children: (A B)
  // Arguments: (C)
  // ---------------------
  // Conclusion: (C),
  //                 where (not A) (not B) and C
  //                   are (> x c) (< x c) and (= x c)
  //                   in some order
  //                 note that "not" here denotes arithmetic negation, flipping
  //                 >= to <, etc.
  ARITH_TRICHOTOMY,

  // ======== Arithmetic operator elimination
  // Children: none
  // Arguments: (t)
  // ---------------------
  // Conclusion: arith::OperatorElim::getAxiomFor(t)
  ARITH_OP_ELIM_AXIOM,

  // ======== Int Trust
  // Children: (P1 ... Pn)
  // Arguments: (Q)
  // ---------------------
  // Conclusion: (Q)
  INT_TRUST,

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
