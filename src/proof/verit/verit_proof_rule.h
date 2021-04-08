/*********************                                                        */
/*! \file verit_proof_rule.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Hanna Lachnitt
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Enumeration of veriT proof rules
 **/

#include <memory>

#include "cvc4_private.h"

#ifndef CVC4__PROOF__VERIT_PROOF_RULE_H
#define CVC4__PROOF__VERIT_PROOF_RULE_H

namespace CVC4 {

namespace proof {

// TODO: Are detailled comments needed?
// + If veriT rules would change, maintenance would be hard
// - Convolution of this file with unnecessary information
enum class VeritRule : uint32_t
{
  //================================================= Special Rules: Commands
  //======================== Anchor and Assume
  // These rules should be printed as commands
  // ======== Anchor
  // Children: (P:F)
  // Arguments:
  // --------------
  // Conclusion: F
  //
  // Each subproof in veriT begins with an anchor command. The outermost
  // application of anchor will not be printed.
  ANCHOR,
  ANCHOR_SUBPROOF,
  ANCHOR_BIND,
  ASSUME,
  //================================================= Rules of the veriT
  // calculus
  // ======== input
  // > i. F
  // , where F is equivalent to a formula asserted in the input problem.
  INPUT,
  // ======== true
  // > i. (true)
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
  // > i. (= (distinct F) true)
  // If applied to terms of type Bool more than two terms can never be distinct.
  // Two cases can be possible: > i. (= (distinct F G) (not (= F G))) > i. (=
  // (distinct F1 F2 F3 ...) false) In general: > i. (= (distinct F1 ... Fn) (
  // )) TODO
  DISTINCT_ELIM,
  // ======== la_rw_eq
  // > i. (= (= F G) (and (<= F G) (<= G F)))
  LA_RW_EQ,
  // TODO
  LA_GENERIC,
  // TODO
  LIA_GENERIC,
  // ======== la_disequality
  // > i. (= (= F G) (not (<= F G)) (not (<= G F)))
  LA_DISEQUALITY,
  LA_TOTALITY,
  LA_TAUTOLOGY,
  FORALL_INST,
  QNT_JOIN,
  QNT_RM_UNUSED,
  TH_RESOLUTION,
  RESOLUTION,
  REFL,
  TRANS,
  CONG,
  AND,
  TAUTOLOGIC_CLAUSE,
  NOT_OR,
  OR,
  NOT_AND,
  XOR1,
  XOR2,
  NOT_XOR1,
  NOT_XOR2,
  IMPLIES,
  NOT_IMPLIES1,
  NOT_IMPLIES2,
  EQUIV1,
  EQUIV2,
  NOT_EQUIV1,
  NOT_EQUIV2,
  ITE1,
  ITE2,
  NOT_ITE1,
  NOT_ITE2,
  ITE_INTRO,
  DUPLICATED_LITERALS,
  CONNECTIVE_DEF,
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
  TMP_AC_SIMP,
  TMP_BFUN_ELIM,
  TEMP_QUANTIFIER_CNF,
  SUBPROOF,
  BIND,
  LET,
  QNT_SIMPLIFY,
  SKO_EX,
  SKO_FORALL,
  /** Special Rules*/
  UNDEFINED,  // TBD
  /** Extended Rules */
  SYMM,
  NOT_SYMM,
  REORDER
};

const char* veritRuletoString(VeritRule id);  // TODO: COMMENT
}  // namespace proof

}  // namespace CVC4

#endif /* CVC4__PROOF__VERIT_PROOF_RULE_H */
