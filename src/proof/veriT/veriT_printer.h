/*********************                                                        */
/*! \file veriT_printer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Hanna Lachnitt
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for printing veriT proof nodes
 **/

#include <memory>
#include "cvc4_private.h"
#include "expr/proof_node_updater.h"
#include "proof/veriT/veriT_post_processor.h"

#ifndef CVC4__PROOF__VERIT_PROOF_PRINTER_H
#define CVC4__PROOF__VERIT_PROOF_PRINTER_H

#include<iostream>

namespace CVC4 {

namespace proof {

enum class VeriTRule : uint32_t
{ 
  //================================================= Special Rules: Commands
	//======================== Anchor and Assume
	//These rules should be printed as commands
	// ======== Anchor
	// Children: (P:F)
	// Arguments:
	// --------------
	// Conclusion: F
	//
	//Each subproof in veriT begins with an anchor command. The outermost application of 
	//anchor will not be printed.
	ANCHOR,
	// ======== Assume
  //In the veriT calculus assumptions are not introduced by a proof rule but by the assume command. 
	ASSUME,

  INPUT,
  TRUE,
  FALSE,
  NOT_NOT,
  AND_POS,
  AND_NEG,
  OR_POS,
  OR_NEG,
  XOR_POS1,
  XOR_POS2,
  XOR_NEG1,
  XOR_NEG2,
  IMPLIES_POS,
  IMPLIES_NEG1,
  IMPLIES_NEG2,
  EQUIV_POS1,
  EQUIV_POS2,
  EQUIV_NEG1,
  EQUIV_NEG2,
  ITE_POS1,
  ITE_POS2,
  ITE_NEG1,
  ITE_NEG2,
  EQ_REFLEXIVE,
  EQ_TRANSITIVE,
  EQ_CONGRUENT,
  EQ_CONGRUENT_PRED,
  DISTINCT_ELIM,
  LA_RW_EQ,
  LA_GENERIC,
  LIA_GENERIC,
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
  DUPLICATE_LITERALS,
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
  TMP_SKOLEMIZE, //SHOULD NOT BE USED, SO DELETE IT AT SOME POINT?
  TEMP_QUANTIFIER_CNF,
  SUBPROOF,
  BIND,
  LET,
  QNT_SIMPLIFY,
  SKO_EX,
  SKO_FORALL
};

static void veriTPrinter(std::ostream& out, 
												 std::shared_ptr<ProofNode> pfn)
{
  // should traverse proof node, print each as a proof step, according to the
  // VERIT_RULE id in the veriTRule enum
  	
	out <<"\n";
	out <<"\n";
	out <<"Print VeriT proof: " << std::endl;
	out <<"\n";
}




}

}

#endif
