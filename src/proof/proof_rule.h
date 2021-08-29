/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Proof rule enumeration.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__PROOF_RULE_H
#define CVC5__PROOF__PROOF_RULE_H

#include <iosfwd>

namespace cvc5 {

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
  // ======== Evaluate
  // Children: none
  // Arguments: (t)
  // ----------------------------------------
  // Conclusion: (= t Evaluator::evaluate(t))
  // Note this is equivalent to:
  //   (REWRITE t MethodId::RW_EVALUATE)
  EVALUATE,
  // ======== Substitution + Rewriting equality introduction
  //
  // In this rule, we provide a term t and conclude that it is equal to its
  // rewritten form under a (proven) substitution.
  //
  // Children: (P1:F1, ..., Pn:Fn)
  // Arguments: (t, (ids (ida (idr)?)?)?)
  // ---------------------------------------------------------------
  // Conclusion: (= t t')
  // where
  //   t' is
  //   Rewriter{idr}(t*sigma{ids, ida}(Fn)*...*sigma{ids, ida}(F1))
  //
  // In other words, from the point of view of Skolem forms, this rule
  // transforms t to t' by standard substitution + rewriting.
  //
  // The arguments ids, ida and idr are optional and specify the identifier of
  // the substitution, the substitution application and rewriter respectively to
  // be used. For details, see theory/builtin/proof_checker.h.
  MACRO_SR_EQ_INTRO,
  // ======== Substitution + Rewriting predicate introduction
  //
  // In this rule, we provide a formula F and conclude it, under the condition
  // that it rewrites to true under a proven substitution.
  //
  // Children: (P1:F1, ..., Pn:Fn)
  // Arguments: (F, (ids (ida (idr)?)?)?)
  // ---------------------------------------------------------------
  // Conclusion: F
  // where
  //   Rewriter{idr}(F*sigma{ids, ida}(Fn)*...*sigma{ids, ida}(F1)) == true
  // where ids and idr are method identifiers.
  //
  // More generally, this rule also holds when:
  //   Rewriter::rewrite(toOriginal(F')) == true
  // where F' is the result of the left hand side of the equality above. Here,
  // notice that we apply rewriting on the original form of F', meaning that
  // this rule may conclude an F whose Skolem form is justified by the
  // definition of its (fresh) Skolem variables. For example, this rule may
  // justify the conclusion (= k t) where k is the purification Skolem for t,
  // e.g. where the original form of k is t.
  //
  // Furthermore, notice that the rewriting and substitution is applied only
  // within the side condition, meaning the rewritten form of the original form
  // of F does not escape this rule.
  MACRO_SR_PRED_INTRO,
  // ======== Substitution + Rewriting predicate elimination
  //
  // In this rule, if we have proven a formula F, then we may conclude its
  // rewritten form under a proven substitution.
  //
  // Children: (P1:F, P2:F1, ..., P_{n+1}:Fn)
  // Arguments: ((ids (ida (idr)?)?)?)
  // ----------------------------------------
  // Conclusion: F'
  // where
  //   F' is
  //   Rewriter{idr}(F*sigma{ids, ida}(Fn)*...*sigma{ids, ida}(F1)).
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
  // Arguments: (G, (ids (ida (idr)?)?)?)
  // ----------------------------------------
  // Conclusion: G
  // where
  //   Rewriter{idr}(F*sigma{ids, ida}(Fn)*...*sigma{ids, ida}(F1)) ==
  //   Rewriter{idr}(G*sigma{ids, ida}(Fn)*...*sigma{ids, ida}(F1))
  //
  // More generally, this rule also holds when:
  //   Rewriter::rewrite(toOriginal(F')) == Rewriter::rewrite(toOriginal(G'))
  // where F' and G' are the result of each side of the equation above. Here,
  // original forms are used in a similar manner to MACRO_SR_PRED_INTRO above.
  MACRO_SR_PRED_TRANSFORM,
  //================================================= Processing rules
  // ======== Remove Term Formulas Axiom
  // Children: none
  // Arguments: (t)
  // ---------------------------------------------------------------
  // Conclusion: RemoveTermFormulas::getAxiomFor(t).
  REMOVE_TERM_FORMULA_AXIOM,

  //================================================= Trusted rules
  // ======== Theory lemma
  // Children: none
  // Arguments: (F, tid)
  // ---------------------------------------------------------------
  // Conclusion: F
  // where F is a (T-valid) theory lemma generated by theory with TheoryId tid.
  // This is a "coarse-grained" rule that is used as a placeholder if a theory
  // did not provide a proof for a lemma or conflict.
  THEORY_LEMMA,
  // ======== Theory Rewrite
  // Children: none
  // Arguments: (F, tid, rid)
  // ----------------------------------------
  // Conclusion: F
  // where F is an equality of the form (= t t') where t' is obtained by
  // applying the kind of rewriting given by the method identifier rid, which
  // is one of:
  //  { RW_REWRITE_THEORY_PRE, RW_REWRITE_THEORY_POST, RW_REWRITE_EQ_EXT }
  // Notice that the checker for this rule does not replay the rewrite to ensure
  // correctness, since theory rewriter methods are not static. For example,
  // the quantifiers rewriter involves constructing new bound variables that are
  // not guaranteed to be consistent on each call.
  THEORY_REWRITE,
  // The remaining rules in this section have the signature of a "trusted rule":
  //
  // Children: ?
  // Arguments: (F)
  // ---------------------------------------------------------------
  // Conclusion: F
  //
  // Unless stated below, the expected children vector of the rule is empty.
  //
  // where F is an equality of the form t = t' where t was replaced by t'
  // based on some preprocessing pass, or otherwise F was added as a new
  // assertion by some preprocessing pass.
  PREPROCESS,
  // where F was added as a new assertion by some preprocessing pass.
  PREPROCESS_LEMMA,
  // where F is an equality of the form t = Theory::ppRewrite(t) for some
  // theory. Notice this is a "trusted" rule.
  THEORY_PREPROCESS,
  // where F was added as a new assertion by theory preprocessing.
  THEORY_PREPROCESS_LEMMA,
  // where F is an equality of the form t = t' where t was replaced by t'
  // based on theory expand definitions.
  THEORY_EXPAND_DEF,
  // where F is an existential (exists ((x T)) (P x)) used for introducing
  // a witness term (witness ((x T)) (P x)).
  WITNESS_AXIOM,
  // where F is an equality (= t t') that holds by a form of rewriting that
  // could not be replayed during proof postprocessing.
  TRUST_REWRITE,
  // where F is an equality (= t t') that holds by a form of substitution that
  // could not be replayed during proof postprocessing.
  TRUST_SUBS,
  // where F is an equality (= t t') that holds by a form of substitution that
  // could not be determined by the TrustSubstitutionMap. This inference may
  // contain possibly multiple children corresponding to the formulas used to
  // derive the substitution.
  TRUST_SUBS_MAP,
  // where F is a solved equality of the form (= x t) derived as the solved
  // form of F', where F' is given as a child.
  TRUST_SUBS_EQ,
  // where F is a fact derived by a theory-specific inference
  THEORY_INFERENCE,
  // ========= SAT Refutation for assumption-based unsat cores
  // Children: (P1, ..., Pn)
  // Arguments: none
  // ---------------------
  // Conclusion: false
  // Note: P1, ..., Pn correspond to the unsat core determined by the SAT
  // solver.
  SAT_REFUTATION,

  //================================================= Boolean rules
  // ======== Resolution
  // Children:
  //  (P1:C1, P2:C2)
  // Arguments: (pol, L)
  // ---------------------
  // Conclusion: C
  // where
  //   - C1 and C2 are nodes viewed as clauses, i.e., either an OR node with
  //     each children viewed as a literal or a node viewed as a literal. Note
  //     that an OR node could also be a literal.
  //   - pol is either true or false, representing the polarity of the pivot on
  //     the first clause
  //   - L is the pivot of the resolution, which occurs as is (resp. under a
  //     NOT) in C1 and negatively (as is) in C2 if pol = true (pol = false).
  //   C is a clause resulting from collecting all the literals in C1, minus the
  //   first occurrence of the pivot or its negation, and C2, minus the first
  //   occurrence of the pivot or its negation, according to the policy above.
  //   If the resulting clause has a single literal, that literal itself is the
  //   result; if it has no literals, then the result is false; otherwise it's
  //   an OR node of the resulting literals.
  //
  //   Note that it may be the case that the pivot does not occur in the
  //   clauses. In this case the rule is not unsound, but it does not correspond
  //   to resolution but rather to a weakening of the clause that did not have a
  //   literal eliminated.
  RESOLUTION,
  // ======== N-ary Resolution
  // Children: (P1:C_1, ..., Pm:C_n)
  // Arguments: (pol_1, L_1, ..., pol_{n-1}, L_{n-1})
  // ---------------------
  // Conclusion: C
  // where
  //   - let C_1 ... C_n be nodes viewed as clauses, as defined above
  //   - let "C_1 <>_{L,pol} C_2" represent the resolution of C_1 with C_2 with
  //     pivot L and polarity pol, as defined above
  //   - let C_1' = C_1 (from P1),
  //   - for each i > 1, let C_i' = C_{i-1} <>_{L_{i-1}, pol_{i-1}} C_i'
  //   The result of the chain resolution is C = C_n'
  CHAIN_RESOLUTION,
  // ======== Factoring
  // Children: (P:C1)
  // Arguments: ()
  // ---------------------
  // Conclusion: C2
  // where
  //  Set representations of C1 and C2 is the same and the number of literals in
  //  C2 is smaller than that of C1
  FACTORING,
  // ======== Reordering
  // Children: (P:C1)
  // Arguments: (C2)
  // ---------------------
  // Conclusion: C2
  // where
  //  Set representations of C1 and C2 are the same and the number of literals
  //  in C2 is the same of that of C1
  REORDERING,
  // ======== N-ary Resolution + Factoring + Reordering
  // Children: (P1:C_1, ..., Pm:C_n)
  // Arguments: (C, pol_1, L_1, ..., pol_{n-1}, L_{n-1})
  // ---------------------
  // Conclusion: C
  // where
  //   - let C_1 ... C_n be nodes viewed as clauses, as defined in RESOLUTION
  //   - let "C_1 <>_{L,pol} C_2" represent the resolution of C_1 with C_2 with
  //     pivot L and polarity pol, as defined in RESOLUTION
  //   - let C_1' be equal, in its set representation, to C_1 (from P1),
  //   - for each i > 1, let C_i' be equal, it its set representation, to
  //     C_{i-1} <>_{L_{i-1}, pol_{i-1}} C_i'
  //   The result of the chain resolution is C, which is equal, in its set
  //   representation, to C_n'
  MACRO_RESOLUTION,
  // As above but not checked
  MACRO_RESOLUTION_TRUST,

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
  // ======== Modus ponens
  // Children: (P1:F1, P2:(=> F1 F2))
  // Arguments: none
  // ---------------------
  // Conclusion: (F2)
  // Note this can optionally be seen as a macro for IMPLIES_ELIM+RESOLUTION.
  MODUS_PONENS,
  // ======== Double negation elimination
  // Children: (P:(not (not F)))
  // Arguments: none
  // ---------------------
  // Conclusion: (F)
  NOT_NOT_ELIM,
  // ======== Contradiction
  // Children: (P1:F P2:(not F))
  // Arguments: ()
  // ---------------------
  // Conclusion: false
  CONTRA,
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
  // ======== Congruence
  // Children: (P1:(= t1 s1), ..., Pn:(= tn sn))
  // Arguments: (<kind> f?)
  // ---------------------------------------------
  // Conclusion: (= (<kind> f? t1 ... tn) (<kind> f? s1 ... sn))
  // Notice that f must be provided iff <kind> is a parameterized kind, e.g.
  // APPLY_UF. The actual node for <kind> is constructible via
  // ProofRuleChecker::mkKindNode.
  CONG,
  // ======== True intro
  // Children: (P:F)
  // Arguments: none
  // ----------------------------------------
  // Conclusion: (= F true)
  TRUE_INTRO,
  // ======== True elim
  // Children: (P:(= F true))
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
  // Children: (P:(= F false))
  // Arguments: none
  // ----------------------------------------
  // Conclusion: (not F)
  FALSE_ELIM,
  // ======== HO trust
  // Children: none
  // Arguments: (t)
  // ---------------------
  // Conclusion: (= t TheoryUfRewriter::getHoApplyForApplyUf(t))
  // For example, this rule concludes (f x y) = (HO_APPLY (HO_APPLY f x) y)
  HO_APP_ENCODE,
  // ======== Congruence
  // Children: (P1:(= f g), P2:(= t1 s1), ..., Pn+1:(= tn sn))
  // Arguments: ()
  // ---------------------------------------------
  // Conclusion: (= (f t1 ... tn) (g s1 ... sn))
  // Notice that this rule is only used when the application kinds are APPLY_UF.
  HO_CONG,

  //================================================= Array rules
  // ======== Read over write
  // Children: (P:(not (= i1 i2)))
  // Arguments: ((select (store a i1 e) i2))
  // ----------------------------------------
  // Conclusion: (= (select (store a i1 e) i2) (select a i2))
  ARRAYS_READ_OVER_WRITE,
  // ======== Read over write, contrapositive
  // Children: (P:(not (= (select (store a i2 e) i1) (select a i1)))
  // Arguments: none
  // ----------------------------------------
  // Conclusion: (= i1 i2)
  ARRAYS_READ_OVER_WRITE_CONTRA,
  // ======== Read over write 1
  // Children: none
  // Arguments: ((select (store a i e) i))
  // ----------------------------------------
  // Conclusion: (= (select (store a i e) i) e)
  ARRAYS_READ_OVER_WRITE_1,
  // ======== Extensionality
  // Children: (P:(not (= a b)))
  // Arguments: none
  // ----------------------------------------
  // Conclusion: (not (= (select a k) (select b k)))
  // where k is arrays::SkolemCache::getExtIndexSkolem((not (= a b))).
  ARRAYS_EXT,
  // ======== EQ_RANGE expansion
  // Children: none
  // Arguments: ((eqrange a b i j))
  // ----------------------------------------
  // Conclusion: (=
  //              (eqrange a b i j)
  //              (forall ((x T))
  //               (=> (and (<= i x) (<= x j)) (= (select a x) (select b x)))))
  ARRAYS_EQ_RANGE_EXPAND,

  //================================================= Bit-Vector rules
  // Note: bitblast() represents the result of the bit-blasted term as a
  //       bit-vector consisting of the output bits of the bit-blasted circuit
  //       representation of the term. Terms are bit-blasted according to the
  //       strategies defined in
  //       theory/bv/bitblast/bitblast_strategies_template.h.
  // ======== Bitblast
  // Children: none
  // Arguments: (t)
  // ---------------------
  // Conclusion: (= t bitblast(t))
  BV_BITBLAST,
  // ======== Bitblast Bit-Vector Constant, Variable
  // Children: none
  // Arguments: (= t bitblast(t))
  // ---------------------
  // Conclusion: (= t bitblast(t))
  // ======== Bitblast Bit-Vector Terms
  // Children: none
  // Arguments: (= (KIND bitblast(child_1) ... bitblast(child_n)) bitblast(t))
  // ---------------------
  // Conclusion: (= (KIND bitblast(child_1) ... bitblast(child_n)) bitblast(t))
  BV_BITBLAST_STEP,

  // ======== Eager Atom
  // Children: none
  // Arguments: (F)
  // ---------------------
  // Conclusion: (= F F[0])
  // where F is of kind BITVECTOR_EAGER_ATOM
  BV_EAGER_ATOM,

  //================================================= Datatype rules
  // ======== Unification
  // Children: (P:(= (C t1 ... tn) (C s1 ... sn)))
  // Arguments: (i)
  // ----------------------------------------
  // Conclusion: (= ti si)
  // where C is a constructor.
  DT_UNIF,
  // ======== Instantiate
  // Children: none
  // Arguments: (t, n)
  // ----------------------------------------
  // Conclusion: (= ((_ is C) t) (= t (C (sel_1 t) ... (sel_n t))))
  // where C is the n^th constructor of the type of T, and (_ is C) is the
  // discriminator (tester) for C.
  DT_INST,
  // ======== Collapse
  // Children: none
  // Arguments: ((sel_i (C_j t_1 ... t_n)))
  // ----------------------------------------
  // Conclusion: (= (sel_i (C_j t_1 ... t_n)) r)
  // where C_j is a constructor, r is t_i if sel_i is a correctly applied
  // selector, or TypeNode::mkGroundTerm() of the proper type otherwise. Notice
  // that the use of mkGroundTerm differs from the rewriter which uses
  // mkGroundValue in this case.
  DT_COLLAPSE,
  // ======== Split
  // Children: none
  // Arguments: (t)
  // ----------------------------------------
  // Conclusion: (or ((_ is C1) t) ... ((_ is Cn) t))
  DT_SPLIT,
  // ======== Clash
  // Children: (P1:((_ is Ci) t), P2: ((_ is Cj) t))
  // Arguments: none
  // ----------------------------------------
  // Conclusion: false
  // for i != j.
  DT_CLASH,

  //================================================= Quantifiers rules
  // ======== Skolem intro
  // Children: none
  // Arguments: (k)
  // ----------------------------------------
  // Conclusion: (= k t)
  // where t is the original form of skolem k.
  SKOLEM_INTRO,
  // ======== Exists intro
  // Children: (P:F[t])
  // Arguments: ((exists ((x T)) F[x]))
  // ----------------------------------------
  // Conclusion: (exists ((x T)) F[x])
  // This rule verifies that F[x] indeed matches F[t] with a substitution
  // over x.
  EXISTS_INTRO,
  // ======== Skolemize
  // Children: (P:(exists ((x1 T1) ... (xn Tn)) F))
  // Arguments: none
  // ----------------------------------------
  // Conclusion: F*sigma
  // sigma maps x1 ... xn to their representative skolems obtained by
  // SkolemManager::mkSkolemize, returned in the skolems argument of that
  // method. Alternatively, can use negated forall as a premise. The witness
  // terms for the returned skolems can be obtained by
  // SkolemManager::getWitnessForm.
  SKOLEMIZE,
  // ======== Instantiate
  // Children: (P:(forall ((x1 T1) ... (xn Tn)) F))
  // Arguments: (t1 ... tn, (id (t)?)? )
  // ----------------------------------------
  // Conclusion: F*sigma
  // where sigma maps x1 ... xn to t1 ... tn.
  //
  // The optional argument id indicates the inference id that caused the
  // instantiation. The term t indicates an additional term (e.g. the trigger)
  // associated with the instantiation, which depends on the id. If the id
  // has prefix "QUANTIFIERS_INST_E_MATCHING", then t is the trigger that
  // generated the instantiation.
  INSTANTIATE,
  // ======== (Trusted) quantifiers preprocess
  // Children: ?
  // Arguments: (F)
  // ---------------------------------------------------------------
  // Conclusion: F
  // where F is an equality of the form t = QuantifiersRewriter::preprocess(t)
  QUANTIFIERS_PREPROCESS,

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
  //   r_t = (skolem (suf t1 (str.len s1)))),
  //   r_s = (skolem (suf s1 (str.len t1)))).
  //
  // or the reverse form of the above:
  //
  // Children: (P1:(= (str.++ t1 t2) (str.++ s1 s2)),
  //            P2:(not (= (str.len t2) (str.len s2))))
  // Arguments: (true)
  // ---------------------
  // Conclusion: (or (= t2 (str.++ r_t s2)) (= s2 (str.++ r_s t2)))
  // where
  //   r_t = (skolem (pre t2 (- (str.len t2) (str.len s2))))),
  //   r_s = (skolem (pre s2 (- (str.len s2) (str.len t2))))).
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
  //   r = (skolem (suf t1 1)).
  //
  // or the reverse form of the above:
  //
  // Children: (P1:(= (str.++ t1 t2) (str.++ s1 c)),
  //            P2:(not (= (str.len t2) 0)))
  // Arguments: (true)
  // ---------------------
  // Conclusion: (= t2 (str.++ r c))
  // where
  //   r = (skolem (pre t2 (- (str.len t2) 1))).
  CONCAT_CSPLIT,
  // ======== Concat length propagate
  // Children: (P1:(= (str.++ t1 t2) (str.++ s1 s2)),
  //            P2:(> (str.len t1) (str.len s1)))
  // Arguments: (false)
  // ---------------------
  // Conclusion: (= t1 (str.++ s1 r_t))
  // where
  //   r_t = (skolem (suf t1 (str.len s1)))
  //
  // or the reverse form of the above:
  //
  // Children: (P1:(= (str.++ t1 t2) (str.++ s1 s2)),
  //            P2:(> (str.len t2) (str.len s2)))
  // Arguments: (false)
  // ---------------------
  // Conclusion: (= t2 (str.++ r_t s2))
  // where
  //   r_t = (skolem (pre t2 (- (str.len t2) (str.len s2)))).
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
  //   r = (skolem (suf t1 (str.len w3))).
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
  //   r = (skolem (pre t2 (- (str.len t2) (str.len w3)))).
  // In other words, w4 is the largest prefix of (pre w2 (- (str.len w2) 1))
  // that can contain a suffix of w1; since t2 is non-empty, w3 must therefore
  // be contained in t2.
  CONCAT_CPROP,
  // ======== String decompose
  // Children: (P1: (>= (str.len t) n)
  // Arguments: (false)
  // ---------------------
  // Conclusion: (and (= t (str.++ w1 w2)) (= (str.len w1) n))
  // or
  // Children: (P1: (>= (str.len t) n)
  // Arguments: (true)
  // ---------------------
  // Conclusion: (and (= t (str.++ w1 w2)) (= (str.len w2) n))
  // where
  //   w1 is (skolem (pre t n))
  //   w2 is (skolem (suf t n))
  STRING_DECOMPOSE,
  // ======== Length positive
  // Children: none
  // Arguments: (t)
  // ---------------------
  // Conclusion: (or (and (= (str.len t) 0) (= t "")) (> (str.len t) 0))
  STRING_LENGTH_POS,
  // ======== Length non-empty
  // Children: (P1:(not (= t "")))
  // Arguments: none
  // ---------------------
  // Conclusion: (not (= (str.len t) 0))
  STRING_LENGTH_NON_EMPTY,
  //======================== Extended functions
  // ======== Reduction
  // Children: none
  // Arguments: (t)
  // ---------------------
  // Conclusion: (and R (= t w))
  // where w = strings::StringsPreprocess::reduce(t, R, ...).
  // In other words, R is the reduction predicate for extended term t, and w is
  //   (skolem t)
  // Notice that the free variables of R are w and the free variables of t.
  STRING_REDUCTION,
  // ======== Eager Reduction
  // Children: none
  // Arguments: (t)
  // ---------------------
  // Conclusion: R
  // where R = strings::TermRegistry::eagerReduce(t).
  STRING_EAGER_REDUCTION,
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
  // Conclusion:(RegExpOpr::reduceRegExpPos((str.in.re t R))),
  // corresponding to the one-step unfolding of the premise.
  RE_UNFOLD_POS,
  // ======== Regular expression unfold negative
  // Children: (P:(not (str.in.re t R)))
  // Arguments: none
  // ---------------------
  // Conclusion:(RegExpOpr::reduceRegExpNeg((not (str.in.re t R)))),
  // corresponding to the one-step unfolding of the premise.
  RE_UNFOLD_NEG,
  // ======== Regular expression unfold negative concat fixed
  // Children: (P:(not (str.in.re t R)))
  // Arguments: none
  // ---------------------
  // Conclusion:(RegExpOpr::reduceRegExpNegConcatFixed((not (str.in.re t
  // R)),L,i)) where RegExpOpr::getRegExpConcatFixed((not (str.in.re t R)), i) =
  // L. corresponding to the one-step unfolding of the premise, optimized for
  // fixed length of component i of the regular expression concatenation R.
  RE_UNFOLD_NEG_CONCAT_FIXED,
  // ======== Regular expression elimination
  // Children: none
  // Arguments: (F, b)
  // ---------------------
  // Conclusion: (= F strings::RegExpElimination::eliminate(F, b))
  // where b is a Boolean indicating whether we are using aggressive
  // eliminations. Notice this rule concludes (= F F) if no eliminations
  // are performed for F.
  RE_ELIM,
  //======================== Code points
  // Children: none
  // Arguments: (t, s)
  // ---------------------
  // Conclusion:(or (= (str.code t) (- 1))
  //                (not (= (str.code t) (str.code s)))
  //                (not (= t s)))
  STRING_CODE_INJ,
  //======================== Sequence unit
  // Children: (P:(= (seq.unit x) (seq.unit y)))
  // Arguments: none
  // ---------------------
  // Conclusion:(= x y)
  // Also applies to the case where (seq.unit y) is a constant sequence
  // of length one.
  STRING_SEQ_UNIT_INJ,

  //================================================= Arithmetic rules
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
  // Conclusion: (>< t1 t2)
  //    where >< is the fusion of the combination of the ><i, (flipping each it
  //    its ki is negative). >< is always one of <, <=
  //    NB: this implies that lower bounds must have negative ki,
  //                      and upper bounds must have positive ki.
  //    t1 is the sum of the scaled polynomials (k_1 * poly_1 + ... + k_n *
  //    poly_n) t2 is the sum of the scaled constants (k_1 * const_1 + ... + k_n
  //    * const_n)
  MACRO_ARITH_SCALE_SUM_UB,
  // ======== Sum Upper Bounds
  // Children: (P1, ... , Pn)
  //           where each Pi has form (><i, Li, Ri)
  //           for ><i in {<, <=, ==}
  // Conclusion: (>< L R)
  //           where >< is < if any ><i is <, and <= otherwise.
  //                 L is (+ L1 ... Ln)
  //                 R is (+ R1 ... Rn)
  ARITH_SUM_UB,
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

  //======== Multiplication sign inference
  // Children: none
  // Arguments: (f1, ..., fk, m)
  // ---------------------
  // Conclusion: (=> (and f1 ... fk) (~ m 0))
  // Where f1, ..., fk are variables compared to zero (less, greater or not
  // equal), m is a monomial from these variables, and ~ is the comparison (less
  // or greater) that results from the signs of the variables. All variables
  // with even exponent in m should be given as not equal to zero while all
  // variables with odd exponent in m should be given as less or greater than
  // zero.
  ARITH_MULT_SIGN,
  //======== Multiplication with positive factor
  // Children: none
  // Arguments: (m, (rel lhs rhs))
  // ---------------------
  // Conclusion: (=> (and (> m 0) (rel lhs rhs)) (rel (* m lhs) (* m rhs)))
  // Where rel is a relation symbol.
  ARITH_MULT_POS,
  //======== Multiplication with negative factor
  // Children: none
  // Arguments: (m, (rel lhs rhs))
  // ---------------------
  // Conclusion: (=> (and (< m 0) (rel lhs rhs)) (rel_inv (* m lhs) (* m rhs)))
  // Where rel is a relation symbol and rel_inv the inverted relation symbol.
  ARITH_MULT_NEG,
  //======== Multiplication tangent plane
  // Children: none
  // Arguments: (t, x, y, a, b, sgn)
  // ---------------------
  // Conclusion:
  //   sgn=-1: (= (<= t tplane) (or (and (<= x a) (>= y b)) (and (>= x a) (<= y
  //   b))) sgn= 1: (= (>= t tplane) (or (and (<= x a) (<= y b)) (and (>= x a)
  //   (>= y b)))
  // Where x,y are real terms (variables or extended terms), t = (* x y)
  // (possibly under rewriting), a,b are real constants, and sgn is either -1
  // or 1. tplane is the tangent plane of x*y at (a,b): b*x + a*y - a*b
  ARITH_MULT_TANGENT,

  // ================ Lemmas for transcendentals
  //======== Assert bounds on PI
  // Children: none
  // Arguments: (l, u)
  // ---------------------
  // Conclusion: (and (>= real.pi l) (<= real.pi u))
  // Where l (u) is a valid lower (upper) bound on pi.
  ARITH_TRANS_PI,
  //======== Exp at negative values
  // Children: none
  // Arguments: (t)
  // ---------------------
  // Conclusion: (= (< t 0) (< (exp t) 1))
  ARITH_TRANS_EXP_NEG,
  //======== Exp is always positive
  // Children: none
  // Arguments: (t)
  // ---------------------
  // Conclusion: (> (exp t) 0)
  ARITH_TRANS_EXP_POSITIVITY,
  //======== Exp grows super-linearly for positive values
  // Children: none
  // Arguments: (t)
  // ---------------------
  // Conclusion: (or (<= t 0) (> exp(t) (+ t 1)))
  ARITH_TRANS_EXP_SUPER_LIN,
  //======== Exp at zero
  // Children: none
  // Arguments: (t)
  // ---------------------
  // Conclusion: (= (= t 0) (= (exp t) 1))
  ARITH_TRANS_EXP_ZERO,
  //======== Exp is approximated from above for negative values
  // Children: none
  // Arguments: (d, t, l, u)
  // ---------------------
  // Conclusion: (=> (and (>= t l) (<= t u)) (<= (exp t) (secant exp l u t))
  // Where d is an even positive number, t an arithmetic term and l (u) a lower
  // (upper) bound on t. Let p be the d'th taylor polynomial at zero (also
  // called the Maclaurin series) of the exponential function. (secant exp l u
  // t) denotes the secant of p from (l, exp(l)) to (u, exp(u)) evaluated at t,
  // calculated as follows:
  //    (p(l) - p(u)) / (l - u) * (t - l) + p(l)
  // The lemma states that if t is between l and u, then (exp t) is below the
  // secant of p from l to u.
  ARITH_TRANS_EXP_APPROX_ABOVE_NEG,
  //======== Exp is approximated from above for positive values
  // Children: none
  // Arguments: (d, t, l, u)
  // ---------------------
  // Conclusion: (=> (and (>= t l) (<= t u)) (<= (exp t) (secant-pos exp l u t))
  // Where d is an even positive number, t an arithmetic term and l (u) a lower
  // (upper) bound on t. Let p* be a modification of the d'th taylor polynomial
  // at zero (also called the Maclaurin series) of the exponential function as
  // follows where p(d-1) is the regular Maclaurin series of degree d-1:
  //    p* = p(d-1) * (1 + t^n / n!)
  // (secant-pos exp l u t) denotes the secant of p from (l, exp(l)) to (u,
  // exp(u)) evaluated at t, calculated as follows:
  //    (p(l) - p(u)) / (l - u) * (t - l) + p(l)
  // The lemma states that if t is between l and u, then (exp t) is below the
  // secant of p from l to u.
  ARITH_TRANS_EXP_APPROX_ABOVE_POS,
  //======== Exp is approximated from below
  // Children: none
  // Arguments: (d, t)
  // ---------------------
  // Conclusion: (>= (exp t) (maclaurin exp d t))
  // Where d is an odd positive number and (maclaurin exp d t) is the d'th
  // taylor polynomial at zero (also called the Maclaurin series) of the
  // exponential function evaluated at t. The Maclaurin series for the
  // exponential function is the following:
  //   e^x = \sum_{n=0}^{\infty} x^n / n!
  ARITH_TRANS_EXP_APPROX_BELOW,
  //======== Sine is always between -1 and 1
  // Children: none
  // Arguments: (t)
  // ---------------------
  // Conclusion: (and (<= (sin t) 1) (>= (sin t) (- 1)))
  ARITH_TRANS_SINE_BOUNDS,
  //======== Sine arg shifted to -pi..pi
  // Children: none
  // Arguments: (x, y, s)
  // ---------------------
  // Conclusion: (and
  //   (<= -pi y pi)
  //   (= (sin y) (sin x))
  //   (ite (<= -pi x pi) (= x y) (= x (+ y (* 2 pi s))))
  // )
  // Where x is the argument to sine, y is a new real skolem that is x shifted
  // into -pi..pi and s is a new integer skolem that is the number of phases y
  // is shifted.
  ARITH_TRANS_SINE_SHIFT,
  //======== Sine is symmetric with respect to negation of the argument
  // Children: none
  // Arguments: (t)
  // ---------------------
  // Conclusion: (= (- (sin t) (sin (- t))) 0)
  ARITH_TRANS_SINE_SYMMETRY,
  //======== Sine is bounded by the tangent at zero
  // Children: none
  // Arguments: (t)
  // ---------------------
  // Conclusion: (and
  //   (=> (> t 0) (< (sin t) t))
  //   (=> (< t 0) (> (sin t) t))
  // )
  ARITH_TRANS_SINE_TANGENT_ZERO,
  //======== Sine is bounded by the tangents at -pi and pi
  // Children: none
  // Arguments: (t)
  // ---------------------
  // Conclusion: (and
  //   (=> (> t -pi) (> (sin t) (- -pi t)))
  //   (=> (< t pi) (< (sin t) (- pi t)))
  // )
  ARITH_TRANS_SINE_TANGENT_PI,
  //======== Sine is approximated from above for negative values
  // Children: none
  // Arguments: (d, t, lb, ub, l, u)
  // ---------------------
  // Conclusion: (=> (and (>= t lb) (<= t ub)) (<= (sin t) (secant sin l u t))
  // Where d is an even positive number, t an arithmetic term, lb (ub) a
  // symbolic lower (upper) bound on t (possibly containing pi) and l (u) the
  // evaluated lower (upper) bound on t. Let p be the d'th taylor polynomial at
  // zero (also called the Maclaurin series) of the sine function. (secant sin l
  // u t) denotes the secant of p from (l, sin(l)) to (u, sin(u)) evaluated at
  // t, calculated as follows:
  //    (p(l) - p(u)) / (l - u) * (t - l) + p(l)
  // The lemma states that if t is between l and u, then (sin t) is below the
  // secant of p from l to u.
  ARITH_TRANS_SINE_APPROX_ABOVE_NEG,
  //======== Sine is approximated from above for positive values
  // Children: none
  // Arguments: (d, t, c, lb, ub)
  // ---------------------
  // Conclusion: (=> (and (>= t lb) (<= t ub)) (<= (sin t) (upper sin c))
  // Where d is an even positive number, t an arithmetic term, c an arithmetic
  // constant, and lb (ub) a symbolic lower (upper) bound on t (possibly
  // containing pi). Let p be the d'th taylor polynomial at zero (also called
  // the Maclaurin series) of the sine function. (upper sin c) denotes the upper
  // bound on sin(c) given by p and lb,ub are such that sin(t) is the maximum of
  // the sine function on (lb,ub).
  ARITH_TRANS_SINE_APPROX_ABOVE_POS,
  //======== Sine is approximated from below for negative values
  // Children: none
  // Arguments: (d, t, c, lb, ub)
  // ---------------------
  // Conclusion: (=> (and (>= t lb) (<= t ub)) (>= (sin t) (lower sin c))
  // Where d is an even positive number, t an arithmetic term, c an arithmetic
  // constant, and lb (ub) a symbolic lower (upper) bound on t (possibly
  // containing pi). Let p be the d'th taylor polynomial at zero (also called
  // the Maclaurin series) of the sine function. (lower sin c) denotes the lower
  // bound on sin(c) given by p and lb,ub are such that sin(t) is the minimum of
  // the sine function on (lb,ub).
  ARITH_TRANS_SINE_APPROX_BELOW_NEG,
  //======== Sine is approximated from below for positive values
  // Children: none
  // Arguments: (d, t, lb, ub, l, u)
  // ---------------------
  // Conclusion: (=> (and (>= t lb) (<= t ub)) (>= (sin t) (secant sin l u t))
  // Where d is an even positive number, t an arithmetic term, lb (ub) a
  // symbolic lower (upper) bound on t (possibly containing pi) and l (u) the
  // evaluated lower (upper) bound on t. Let p be the d'th taylor polynomial at
  // zero (also called the Maclaurin series) of the sine function. (secant sin l
  // u t) denotes the secant of p from (l, sin(l)) to (u, sin(u)) evaluated at
  // t, calculated as follows:
  //    (p(l) - p(u)) / (l - u) * (t - l) + p(l)
  // The lemma states that if t is between l and u, then (sin t) is above the
  // secant of p from l to u.
  ARITH_TRANS_SINE_APPROX_BELOW_POS,

  // ================ CAD Lemmas
  // We use IRP for IndexedRootPredicate.
  //
  // A formula "Interval" describes that a variable (xn is none is given) is
  // within a particular interval whose bounds are given as IRPs. It is either
  // an open interval or a point interval:
  //   (IRP k poly) < xn < (IRP k poly)
  //   xn == (IRP k poly)
  //
  // A formula "Cell" describes a portion
  // of the real space in the following form:
  //   Interval(x1) and Interval(x2) and ...
  // We implicitly assume a Cell to go up to n-1 (and can be empty).
  //
  // A formula "Covering" is a set of Intervals, implying that xn can be in
  // neither of these intervals. To be a covering (of the real line), the union
  // of these intervals should be the real numbers.
  // ======== CAD direct conflict
  // Children (Cell, A)
  // ---------------------
  // Conclusion: (false)
  // A direct interval is generated from an assumption A (in variables x1...xn)
  // over a Cell (in variables x1...xn). It derives that A evaluates to false
  // over the Cell. In the actual algorithm, it means that xn can not be in the
  // topmost interval of the Cell.
  ARITH_NL_CAD_DIRECT,
  // ======== CAD recursive interval
  // Children (Cell, Covering)
  // ---------------------
  // Conclusion: (false)
  // A recursive interval is generated from a Covering (for xn) over a Cell
  // (in variables x1...xn-1). It generates the conclusion that no xn exists
  // that extends the Cell and satisfies all assumptions.
  ARITH_NL_CAD_RECURSIVE,

  //================================================ Place holder for Lfsc rules
  // ======== Lfsc rule
  // Children: (P1 ... Pn)
  // Arguments: (id, Q, A1, ..., Am)
  // ---------------------
  // Conclusion: (Q)
  LFSC_RULE,

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

/** Hash function for proof rules */
struct PfRuleHashFunction
{
  size_t operator()(PfRule id) const;
}; /* struct PfRuleHashFunction */

}  // namespace cvc5

#endif /* CVC5__PROOF__PROOF_RULE_H */
