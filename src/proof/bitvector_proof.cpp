/*********************                                                        */
/*! \file uf_proof.cpp
** \verbatim
** Original author: Liana Hadarean
** Major contributors: none
** Minor contributors (to current version): none
** This file is part of the CVC4 project.
** Copyright (c) 2009-2014  New York University and The University of Iowa
** See the file COPYING in the top-level source directory for licensing
** information.\endverbatim
**
** \brief [[ Add one-line brief description here ]]
**
** [[ Add lengthier description here ]]
** \todo document this file
**/

#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"
#include "proof/bitvector_proof.h"
#include "proof/sat_proof_implementation.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;

std::string toLFSCBVKind(Kind kind);

BitVectorProof::BitVectorProof(theory::bv::TheoryBV* bv, TheoryProofEngine* proofEngine)
  : TheoryProof(bv, proofEngine)
  , d_declarations()
  , d_resolutionProof(NULL)
    //  , d_cnfProof()
{}

void BitVectorProof::initSatProof(::BVMinisat::Solver* solver) {
  Assert (d_resolutionProof == NULL);
  d_resolutionProof = new LFSCBVSatProof(solver);
}

BVSatProof* BitVectorProof::getSatProof() {
  Assert (d_resolutionProof != NULL);
  return d_resolutionProof;
}

void BitVectorProof::registerTerm(Expr term) {
  if (term.getKind() == kind::VARIABLE ||
      term.getKind() == kind::SKOLEM) {
    d_declarations.insert(term);
  }
  // don't care about parametric operators for bv?
  for (unsigned i = 0; i < term.getNumChildren(); ++i) {
    d_proofEngine->registerTerm(term[i]); 
  }
}

void BitVectorProof::startBVConflict(::BVMinisat::TCRef cr) {
  d_satProof->startResChain(cr);
}
void BitVectorProof::endBVConflict(std::vector<::BVMinisat::TLit>& confl) {
  std::vector<Expr> expr_confl;
  for (unsigned i = 0; i < confl.size(); ++i) {
    Assert (d_satProof->isAssumption(confl[i]));
    Expr expr_lit = d_cnf->getAtom(lit);
    expr_confl.push_back(expr_lit); 
  }
  Node conflict = Rewriter::rewrite(utils::mkAnd(expr_confl));
  
  Assert (d_conflictMap.find(conflict) == d_conflictMap.end());
  // we don't need to check for uniqueness in the sat solver then        
  ClauseId clause_id = d_satProof->registerAssumptionConflict(confl);
  d_conflictMap[confl] = clause_id;
  d_satProof->endResChain(clause_id);
}

void BitVectorProof::finalizeConflicts(std::vector<Expr>& conflicts) {
  for (
  for(unsigned i = 0; i < conflics.size(); ++i) {
    Expr confl = concflicts[i];
    Assert (d_lemmaMap.find(confl) != d_lemmaMap.end()); 
  }
}

void LFSCBitVectorProof::printTerm(Expr term, std::ostream& os) {
  Assert (Theory::theoryOf(term) == THEORY_BV);
  
  switch (term.getKind()) {
  case kind::CONST_BITVECTOR : {
    printConstant(term, os);
    return; 
  }
  case kind::BITVECTOR_AND : 
  case kind::BITVECTOR_OR :
  case kind::BITVECTOR_XOR :
  case kind::BITVECTOR_NAND :
  case kind::BITVECTOR_NOR :
  case kind::BITVECTOR_XNOR :
  case kind::BITVECTOR_COMP :
  case kind::BITVECTOR_MULT :
  case kind::BITVECTOR_PLUS :
  case kind::BITVECTOR_SUB :
  case kind::BITVECTOR_UDIV :
  case kind::BITVECTOR_UREM :
  case kind::BITVECTOR_SDIV :
  case kind::BITVECTOR_SREM :
  case kind::BITVECTOR_SMOD :
  case kind::BITVECTOR_SHL :
  case kind::BITVECTOR_LSHR :
  case kind::BITVECTOR_ASHR :
  case kind::BITVECTOR_CONCAT : {
    printOperatorNary(term, os);
    return;
  }
  case kind::BITVECTOR_NEG :
  case kind::BITVECTOR_NOT :
  case kind::BITVECTOR_ROTATE_LEFT :
  case kind::BITVECTOR_ROTATE_RIGHT : {
    printOperatorUnary(term, os);
    return;
  }
  case kind::BITVECTOR_ULT :
  case kind::BITVECTOR_ULE :
  case kind::BITVECTOR_UGT :
  case kind::BITVECTOR_UGE :
  case kind::BITVECTOR_SLT :
  case kind::BITVECTOR_SLE :
  case kind::BITVECTOR_SGT :
  case kind::BITVECTOR_SGE : {
    printPredicate(term, os);
    return;
  }
  case kind::BITVECTOR_EXTRACT :
  case kind::BITVECTOR_REPEAT :
  case kind::BITVECTOR_ZERO_EXTEND :
  case kind::BITVECTOR_SIGN_EXTEND : {
    printOperatorParametric(term, os);
    return;
  }
  case kind::BITVECTOR_BITOF : {
    Unreachable("Need to figure out");
    return;
  }
  case kind::VARIABLE:
  case kind::SKOLEM: {
    os << "(a_var_bv " << term <<")";
    return;
  }
  default:
    Unreachable(); 
  }
}

void LFSCBitVectorProof::printConstant(Expr term, std::ostream& os) {
  Assert (term.isConst());
  os <<"(a_bv ";
  std::ostringstream paren;
  TNode node = Node::fromExpr(term); 
  for (unsigned i = 0; i < utils::getSize(node); ++i) {
    os << "(bvc ";
    os << (utils::getBit(node, i) ? "b1" : "b0") <<" "; 
    paren << ")";
  }
  os << " bvn)";
  os << paren.str(); 
}

void LFSCBitVectorProof::printOperatorNary(Expr term, std::ostream& os) {
  std::string op = toLFSCBVKind(term.getKind());
  std::ostringstream paren;
  os <<"("<< op <<" ";
  for (unsigned i = 0; i < term.getNumChildren(); ++i) {
    d_proofEngine->printTerm(term[i], os);
    os << " ";
    if (i + 2 < term.getNumChildren()) {
      os <<"(" << op <<" ";
      paren <<")";
    }
  }
  os <<")";
}

void LFSCBitVectorProof::printOperatorUnary(Expr term, std::ostream& os) {
  os <<"(";
  os << toLFSCBVKind(term.getKind());
  os << " ";
  d_proofEngine->printTerm(term[0], os); 
  os <<")";
}

void LFSCBitVectorProof::printPredicate(Expr term, std::ostream& os) {
  os <<"(";
  os << toLFSCBVKind(term.getKind());
  os << " ";
  d_proofEngine->printTerm(term[0], os);
  os << " ";
  d_proofEngine->printTerm(term[1], os); 
  os <<")";
}

void LFSCBitVectorProof::printOperatorParametric(Expr term, std::ostream& os) {
  os <<"(";  
  os << toLFSCBVKind(term.getKind()); 
  os <<" "; 
  if (term.getKind() == kind::BITVECTOR_REPEAT) {
    unsigned amount = term.getOperator().getConst<BitVectorRepeat>().repeatAmount;
    os << amount; 
  }
  if (term.getKind() == kind::BITVECTOR_SIGN_EXTEND) {
    unsigned amount = term.getOperator().getConst<BitVectorSignExtend>().signExtendAmount;
    os << amount; 
  }

  if (term.getKind() == kind::BITVECTOR_ZERO_EXTEND) {
    unsigned amount = term.getOperator().getConst<BitVectorZeroExtend>().zeroExtendAmount;
    os << amount; 
  }
  if (term.getKind() == kind::BITVECTOR_EXTRACT) {
    unsigned low = utils::getExtractLow(Node::fromExpr(term));
    unsigned high = utils::getExtractHigh(Node::fromExpr(term));
    os << high <<" " << low; 
  }
  os <<" ";
  Assert (term.getNumChildren() == 1); 
  d_proofEngine->printTerm(term[0], os);
  os <<")";
}

void LFSCBitVectorProof::printSort(Type type, std::ostream& os) {
  Assert (type.isBitVector()); 
  os << "BitVec ";  
}

void LFSCBitVectorProof::printTheoryLemmaProof(std::vector<Expr>& lemma, std::ostream& os, std::ostream& paren) {
  os << ";; TODO print bit-vector lemma proof \n ;;";
  for (unsigned i = 0; i < lemma.size(); ++i) {
    os << lemma[i] << " "; 
  }
  os << "\n"; 

  os << "(clausify_false trust)\n"; 
}
void LFSCBitVectorProof::printDeclarations(std::ostream& os, std::ostream& paren) {
  ExprSet::const_iterator it = d_declarations.begin();
  ExprSet::const_iterator end = d_declarations.end();
  for (; it != end; ++it) {
    os << "(% " << *it <<" var_bv\n";
    paren <<")"; 
  }
}
void LFSCBitVectorProof::printBitblasting(std::ostream& os, std::ostream& paren) {
  os << ";; TODO print bit-blasting \n";
}

std::string toLFSCBVKind(Kind kind) {
  switch(kind) {
  case kind::BITVECTOR_AND :
    return "bvand"; 
  case kind::BITVECTOR_OR :
    return "bvor"; 
  case kind::BITVECTOR_XOR :
    return "bvxor"; 
  case kind::BITVECTOR_NAND :
    return "bvnand"; 
  case kind::BITVECTOR_NOR :
    return "bvnor"; 
  case kind::BITVECTOR_XNOR :
    return "bvxnor"; 
  case kind::BITVECTOR_COMP :
    return "bvcomp"; 
  case kind::BITVECTOR_MULT :
    return "bvmul";
  case kind::BITVECTOR_PLUS :
    return "bvadd"; 
  case kind::BITVECTOR_SUB :
    return "bvsub";
  case kind::BITVECTOR_UDIV :
    return "bvudiv";
  case kind::BITVECTOR_UREM :
    return "bvurem"; 
  case kind::BITVECTOR_SDIV :
    return "bvsdiv"; 
  case kind::BITVECTOR_SREM :
    return "bvsrem";
  case kind::BITVECTOR_SMOD :
    return "bvsmod"; 
  case kind::BITVECTOR_SHL :
    return "bvshl"; 
  case kind::BITVECTOR_LSHR :
    return "bvlshr";
  case kind::BITVECTOR_ASHR :
    return "bvashr";
  case kind::BITVECTOR_CONCAT :
    return "concat"; 
  case kind::BITVECTOR_NEG :
    return "bvneg"; 
  case kind::BITVECTOR_NOT :
    return "bvnot"; 
  case kind::BITVECTOR_ROTATE_LEFT :
    return "rotate_left"; 
  case kind::BITVECTOR_ROTATE_RIGHT :
    return "rotate_right";
  case kind::BITVECTOR_ULT :
    return "bvult"; 
  case kind::BITVECTOR_ULE :
    return "bvule"; 
  case kind::BITVECTOR_UGT :
    return "bvugt";
  case kind::BITVECTOR_UGE :
    return "bvuge";
  case kind::BITVECTOR_SLT :
    return "bvslt"; 
  case kind::BITVECTOR_SLE :
    return "bvsle"; 
  case kind::BITVECTOR_SGT :
    return "bvsgt"; 
  case kind::BITVECTOR_SGE :
    return "bvsge"; 
  case kind::BITVECTOR_EXTRACT :
    return "extract"; 
  case kind::BITVECTOR_REPEAT :
    return "repeat"; 
  case kind::BITVECTOR_ZERO_EXTEND :
    return "zero_extend";
  case kind::BITVECTOR_SIGN_EXTEND :
    return "sign_extend"; 
  default:
    Unreachable();
  }
}
