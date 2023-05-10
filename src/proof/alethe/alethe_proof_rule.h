/******************************************************************************
 * Top contributors (to current version):
 *   Hanna Lachnitt, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Enumeration of Alethe proof rules
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__ALETHE__ALETHE_PROOF_RULE_H
#define CVC5__PROOF__ALETHE__ALETHE_PROOF_RULE_H

#include <iostream>

#include "expr/node.h"

namespace cvc5::internal {

namespace proof {

enum class AletheRule : uint32_t
{
  // This enumeration lists all Alethe proof rules. For each rule a list of
  // steps is given. The last step is the conclusion obtained by applying the
  // rule in question. There might be zero or more steps occuring before the
  // conclusion in the proof. A step has the form:
  //
  //   G > i. F
  // where G is a context, i is an id and F is a formula. A context may include
  // substitutions x->y and fixed variables x. For more details see
  // https://verit.loria.fr/documentation/alethe-spec.pdf
  //
  //================================================= Special Rules: Commands
  // These rules should be printed as commands
  //
  // ======== subproof
  // > i1. F1
  // ...
  // > in. Fn
  // ...
  // > j. F
  // ---------------------------------
  // > k. (cl (not F1) ... (not Fn) F)
  //
  // Each subproof in Alethe begins with an anchor command. The outermost
  // application of ANCHOR_SUBPROOF will not be printed.
  ANCHOR_SUBPROOF,
  // ======== bind
  // G,y1,...,yn,x1->y1,...,xn->yn > j.  (= F1 F2)
  // ------------------------------------------------------
  // G > k. (= (forall (x1 ... xn) F1) (forall (y1 ... yn) F2))
  //
  // where y1,...,yn are not free in (forall (x1,...,xn) F2)
  ANCHOR_BIND,
  // ======== skolemization rules
  // G,x->(choice (x) F1) > j.  (= F1 F2)
  // ------------------------------------
  // G > k. (= (exists (x) F1) F2)
  //
  // G,x->(choice (x) (not F1)) > j.  (= F1 F2)
  // ------------------------------------------
  // G > k. (= (forall (x) F1) F2)
  ANCHOR_SKO_FORALL,
  ANCHOR_SKO_EX,
  // ======== input
  // > i. F
  ASSUME,
  //================================================= Rules of the Alethe
  // calculus
  //
  // ======== true
  // > i. true
  TRUE,
  // ======== false
  // > i. (not true)
  FALSE,
  // ======== not_not
  // > i.  (cl (not(not(not F)))  F)
  NOT_NOT,
  // ======== and_pos
  // > i.  (cl (not(and F1 ... Fn))  Fi)
  // , with 1 <= i <= n
  AND_POS,
  // ======== and_neg
  // > i.  (cl (and F1 ... Fn) (not F1) ... (not Fn))
  AND_NEG,
  // ======== or_pos
  // > i.  (cl (not (or F1 ... Fn)) (not F1) ... (not Fn))
  OR_POS,
  // ======== or_neg
  // > i.  (cl (or F1 ... Fn) (not Fi))
  // , with 1 <= i <= n
  OR_NEG,
  // ======== xor_pos1
  // > i.  (cl (not (xor F1 F2)) F1 F2)
  XOR_POS1,
  // ======== xor_pos2
  // > i.  (cl (not (xor F1 F2)) (not F1) (not F2))
  XOR_POS2,
  // ======== xor_neg1
  // > i.  (cl (xor F1 F2) F1 (not F2))
  XOR_NEG1,
  // ======== xor_neg2
  // > i.  (cl (xor F1 F2) (not F1) F2)
  XOR_NEG2,
  // ======== implies_pos
  // > i.  (cl (not (implies F1 F2)) (not F1) F2)
  IMPLIES_POS,
  // ======== implies_neg1
  // > i.  (cl (implies F1 F2) F1)
  IMPLIES_NEG1,
  // ======== implies_neg2
  // > i.  (cl (implies F1 F2) (not F2))
  IMPLIES_NEG2,
  // ======== equiv_pos1
  // > i.  (cl (not (= F1 F2)) F1 (not F2))
  EQUIV_POS1,
  // ======== equiv_pos2
  // > i.  (cl (not (= F1 F2)) (not F1) F2)
  EQUIV_POS2,
  // ======== equiv_neg1
  // > i.  (cl (= F1 F2) (not F1) (not F2))
  EQUIV_NEG1,
  // ======== equiv_neg2
  // > i.  (cl (= F1 F2) F1 F2)
  EQUIV_NEG2,
  // ======== ite_pos1
  // > i.  (cl (not (ite F1 F2 F3)) F1 F3)
  ITE_POS1,
  // ======== ite_pos2
  // > i.  (cl (not (ite F1 F2 F3)) (not F1) F2)
  ITE_POS2,
  // ======== ite_neg1
  // > i.  (cl (ite F1 F2 F3) F1 (not F3))
  ITE_NEG1,
  // ======== ite_neg2
  // > i.  (cl (ite F1 F2 F3) (not F1) (not F2))
  ITE_NEG2,
  // ======== eq_reflexive
  // > i.  (= F F)
  EQ_REFLEXIVE,
  // ======== eq_transitive
  // > i.  (cl (not (= F1 F2)) ... (not (= F_{n-1} Fn)) (= F1 Fn))
  EQ_TRANSITIVE,
  // ======== eq_congruent
  // > i.  (cl (not (= F1 G1)) ... (not (= Fn Gn)) (= f(F1,...,Fn)
  // f(G1,...,Gn)))
  EQ_CONGRUENT,
  // ======== eq_congruent_pred
  // > i.  (cl (not (= F1 G1)) ... (not (= Fn Gn)) (= P(F1,...,Fn)
  // P(G1,...,Gn)))
  EQ_CONGRUENT_PRED,
  // ======== distinct_elim
  // If called with one argument:
  //  > i. (= (distinct F) true)
  // If applied to terms of type Bool more than two terms can never be distinct.
  // Two cases can be possible:
  //  > i. (= (distinct F G) (not (= F G)))
  // and
  //  > i. (= (distinct F1 F2 F3 ...) false)
  // In general:
  //  > i. (= (distinct F1 ... Fn) (AND^n_i=1 (AND^n_j=i+1 (!= Fi Fj))))
  DISTINCT_ELIM,
  // ======== la_rw_eq
  // > i. (= (= F G) (and (<= F G) (<= G F)))
  LA_RW_EQ,
  // Tautology of linear disequalities.
  // > i. (cl F1 ... Fn)
  LA_GENERIC,
  // Tautology for multiplying both sides of inequality by positive factor
  LA_MULT_POS,
  // Tautology for multiplying both sides of inequality by negative factor
  LA_MULT_NEG,
  // Tautology of linear integer arithmetic
  // > i. (cl F1 ... Fn)
  LIA_GENERIC,
  // ======== la_disequality
  // > i. (= (= F G) (not (<= F G)) (not (<= G F)))
  LA_DISEQUALITY,
  // ======== la_totality
  // > i. (or (<= t1 t2) (<= t2 t1))
  LA_TOTALITY,
  // ======== la_tautology
  // Tautology of linear arithmetic that can be checked without sophisticated
  // reasoning.
  LA_TAUTOLOGY,
  // ======== forall_inst
  // > i. (or (not (forall (x1 ... xn) P)) P[t1/x1]...[tn/xn])
  // args = ((:= x_k1 tk1) ... (:= xkn tkn))
  // where k1,...,kn is a permutation of 1,...,n and xi and ki have the same
  // sort.
  FORALL_INST,
  // ======== qnt_join
  // G > i. (= (Q (x1 ... xn) (Q (xn+1 ... xm) F)) (Q (xk1 ... xko) F))
  // where m>n, Q in {forall,exist}, k1...ko is a monotonic map 1,...,m s.t.
  // xk1,...,xko are pairwise distinct and {x1,...,xm} = {xk1,...,xko}.
  QNT_JOIN,
  // ======== qnt_tm_unused
  // G > i. (= (Q (x1 ... xn) F) (Q (xk1 ... xkm) F))
  // where m <= n, Q in {forall,exists}, k1,...,km is monotonic map to 1,...,n
  // and if x in {xj | j in {1,...,n} and j not in {k1,...,km}} then x is not
  // free in P
  QNT_RM_UNUSED,
  // ======== th_resolution
  // > i1. (cl F^1_1 ... F^1_k1)
  // ...
  // > in. (cl F^n_1 ... F^n_kn)
  // ...
  // > i1,...,in. (cl F^r1_s1 ... F^rm_sm)
  // where (cl F^r1_s1 ... F^rm_sm) are from F^i_j and are the result of a chain
  // of predicate resolution steps on the clauses i1 to in. This rule is used
  // when the resolution step is not emitted by the SAT solver.
  TH_RESOLUTION,
  // ======== resolution
  // This rule is equivalent to the th_resolution rule but is emitted by the SAT
  // solver.
  RESOLUTION,
  // ======== resolution from CHAIN_RESOLUTION or RESOLUTIONS
  // Same as resolution but premises might have been printed as (cl (or F1 ...
  // Fn)) instead of (cl F1 ... Fn)
  RESOLUTION_OR,
  // ======== refl
  // G > i. (= F1 F2)
  REFL,
  // ======== trans
  // G > i. (= F1 F2)
  // ...
  // G > j. (= F2 F3)
  // ...
  // G > k. (= F1 F3)
  TRANS,
  // ======== cong
  // G > i1. (= F1 G1)
  // ...
  // G > in. (= Fn Gn)
  // ...
  // G > j. (= (f F1 ... Fn) (f G1 ... Gn))
  // where f is an n-ary function symbol.
  CONG,
  // ======== and
  // > i. (and F1 ... Fn)
  // ...
  // > j. Fi
  AND,
  // ======== tautologic_clause
  // > i. (cl F1 ... Fi ... Fj ... Fn)
  // ...
  // > j. true
  // where Fi != Fj
  TAUTOLOGIC_CLAUSE,
  // ======== not_or
  // > i. (not (or F1 ... Fn))
  // ...
  // > j. (not Fi)
  NOT_OR,
  // ======== or
  // > i. (or F1 ... Fn)
  // ...
  // > j. (cl F1 ... Fn)
  OR,
  // ======== not_and
  // > i. (not (and F1 ... Fn))
  // ...
  // > j. (cl (not F1) ... (not Fn))
  NOT_AND,
  // ======== xor1
  // > i. (xor F1 F2)
  // ...
  // > j. (cl F1 F2)
  XOR1,
  // ======== xor2
  // > i. (xor F1 F2)
  // ...
  // > j. (cl (not F1) (not F2))
  XOR2,
  // ======== not_xor1
  // > i. (not (xor F1 F2))
  // ...
  // > j. (cl F1 (not F2))
  NOT_XOR1,
  // ======== not_xor2
  // > i. (not (xor F1 F2))
  // ...
  // > j. (cl (not F1) F2)
  NOT_XOR2,
  // ======== implies
  // > i. (=> F1 F2)
  // ...
  // > j. (cl (not F1) F2)
  IMPLIES,
  // ======== not_implies1
  // > i. (not (=> F1 F2))
  // ...
  // > j. (not F2)
  NOT_IMPLIES1,
  // ======== not_implies2
  // > i. (not (=> F1 F2))
  // ...
  // > j. (not F2)
  NOT_IMPLIES2,
  // ======== equiv1
  // > i. (= F1 F2)
  // ...
  // > j. (cl (not F1) F2)
  EQUIV1,
  // ======== equiv2
  // > i. (= F1 F2)
  // ...
  // > j. (cl F1 (not F2))
  EQUIV2,
  // ======== not_equiv1
  // > i. (not (= F1 F2))
  // ...
  // > j. (cl F1 F2)
  NOT_EQUIV1,
  // ======== not_equiv2
  // > i. (not (= F1 F2))
  // ...
  // > j. (cl (not F1) (not F2))
  NOT_EQUIV2,
  // ======== ite1
  // > i. (ite F1 F2 F3)
  // ...
  // > j. (cl F1 F3)
  ITE1,
  // ======== ite2
  // > i. (ite F1 F2 F3)
  // ...
  // > j. (cl (not F1) F2)
  ITE2,
  // ======== not_ite1
  // > i. (not (ite F1 F2 F3))
  // ...
  // > j. (cl F1 (not F3))
  NOT_ITE1,
  // ======== not_ite2
  // > i. (not (ite F1 F2 F3))
  // ...
  // > j. (cl (not F1) (not F3))
  NOT_ITE2,
  // ======== ite_intro
  // > i. (= F (and F F1 ... Fn))
  // where F contains the ite operator. Let G1,...,Gn be the terms starting with
  // ite, i.e. Gi := (ite Fi Hi Hi'), then Fi = (ite Fi (= Gi Hi) (= Gi Hi')) if
  // Hi is of sort Bool
  ITE_INTRO,
  // ======== contraction
  // > i. (cl F1 ... Fn)
  // ...
  // > j. (cl Fk1 ... Fkm)
  // where m <= n and k1,...,km is a monotonic map to 1,...,n such that Fk1 ...
  // Fkm are pairwise distinct and {F1,...,Fn} = {Fk1 ... Fkm}
  CONTRACTION,
  // ======== connective_def
  //  G > i. (= (xor F1 F2) (or (and (not F1) F2) (and F1 (not F2))))
  // or
  //  G > i. (= (= F1 F2) (and (=> F1 F2) (=> F2 F1)))
  // or
  //  G > i. (= (ite F1 F2 F3) (and (=> F1 F2) (=> (not F1) (not F3))))
  CONNECTIVE_DEF,
  // ======== Simplify rules
  // The following rules are simplifying rules introduced as tautologies that
  // can be verified by a number of simple transformations
  ITE_SIMPLIFY,
  EQ_SIMPLIFY,
  AND_SIMPLIFY,
  OR_SIMPLIFY,
  NOT_SIMPLIFY,
  IMPLIES_SIMPLIFY,
  EQUIV_SIMPLIFY,
  BOOL_SIMPLIFY,
  QUANTIFIER_SIMPLIFY,
  DIV_SIMPLIFY,
  PROD_SIMPLIFY,
  UNARY_MINUS_SIMPLIFY,
  MINUS_SIMPLIFY,
  SUM_SIMPLIFY,
  COMP_SIMPLIFY,
  NARY_ELIM,
  QNT_SIMPLIFY,
  ALL_SIMPLIFY,
  // ======== let
  // G,x1->F1,...,xn->Fn > j. (= G G')
  // ---------------------------------
  // G > k. (= (let (x1 := F1,...,xn := Fn.G) G')
  LET,
  // ======== sko_ex
  // G,x1->(e x1.F),...,xn->(e xn.F) > j. (= F G)
  // --------------------------------------------
  // G > k. (exists (x1 ... xn) (= F G))
  SKO_EX,
  // ======== sko_forall
  // G,x1->(e x1.(not F)),...,xn->(e xn.(not F)) > j. (= F G)
  // --------------------------------------------------------
  // G > k. (forall (x1 ... xn) (= F G))
  SKO_FORALL,
  // ======== symm
  // > i. (= F G)
  // ...
  // > j. (= G F)
  SYMM,
  // ======== not_symm
  // > i. (not (= F G))
  // ...
  // > j. (not (= G F))
  NOT_SYMM,
  // ======== reorder
  // > i1. F1
  // ...
  // > j. F2
  // where set representation of F1 and F2 are the same and the number of
  // literals in C2 is the same of that of C1.
  REORDERING,
  // ======== bitvector
  //  > i. (cl (= t bbt(t)))
  BV_BITBLAST_STEP_VAR,
  BV_BITBLAST_STEP_BVAND,
  BV_BITBLAST_STEP_BVOR,
  BV_BITBLAST_STEP_BVXOR,
  BV_BITBLAST_STEP_BVXNOR,
  BV_BITBLAST_STEP_BVNOT,
  BV_BITBLAST_STEP_BVADD,
  BV_BITBLAST_STEP_BVNEG,
  BV_BITBLAST_STEP_BVMULT,
  BV_BITBLAST_STEP_BVULE,
  BV_BITBLAST_STEP_BVULT,
  BV_BITBLAST_STEP_EXTRACT,
  BV_BITBLAST_STEP_BVEQUAL,
  BV_BITBLAST_STEP_CONCAT,
  BV_BITBLAST_STEP_CONST,
  // ======== hole
  // Used for unjustified steps
  HOLE,
  // ======== undefined
  // Used in case that a step in the proof rule could not be translated.
  UNDEFINED
};

/**
 * Converts an Alethe proof rule to a string.
 *
 * @param id The Alethe proof rule
 * @return The name of the Alethe proof rule
 */
const char* aletheRuleToString(AletheRule id);

/**
 * Writes an Alethe proof rule name to a stream.
 *
 * @param out The stream to write to
 * @param id The Alethe proof rule to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, AletheRule id);

/** Convert a node holding an id to the corresponding AletheRule */
AletheRule getAletheRule(Node n);

}  // namespace proof

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__ALETHE__ALETHE_PROOF_RULE_H */
