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
#include "proof/bitvector_proof.h"
#include "proof/sat_proof_implementation.h"
#include "proof/proof_utils.h"
#include "prop/bvminisat/bvminisat.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;

std::string toLFSCBVKind(Kind kind);

BitVectorProof::BitVectorProof(theory::bv::TheoryBV* bv, TheoryProofEngine* proofEngine)
  : TheoryProof(bv, proofEngine)
  , d_declarations()
  , d_resolutionProof(NULL)
  , d_cnfProof(NULL)
{}

void BitVectorProof::initSatProof(::BVMinisat::Solver* solver) {
  Assert (d_resolutionProof == NULL);
  d_resolutionProof = new LFSCBVSatProof(solver, "bb", true);
}

void BitVectorProof::initCnfProof(prop::CnfStream* cnfStream) {
  Assert (d_cnfProof == NULL);
  d_cnfProof = new LFSCCnfProof(cnfStream, "bb");
  Assert (d_resolutionProof != NULL);
  d_resolutionProof->setCnfProof(d_cnfProof); 
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

void BitVectorProof::startBVConflict(::BVMinisat::Solver::TCRef cr) {
  d_resolutionProof->startResChain(cr);
}
void BitVectorProof::endBVConflict(const BVMinisat::Solver::TLitVec& confl) {
  std::vector<Expr> expr_confl;
  for (int i = 0; i < confl.size(); ++i) {
    prop::SatLiteral lit = prop::BVMinisatSatSolver::toSatLiteral(confl[i]);
    Expr atom = d_cnfProof->getAtom(lit.getSatVariable());
    Expr expr_lit = lit.isNegated() ? atom.notExpr() : atom; 
    expr_confl.push_back(expr_lit); 
  }
  Expr conflict = utils::mkSortedExpr(kind::OR, expr_confl);
  
  Assert (d_conflictMap.find(conflict) == d_conflictMap.end());
  // we don't need to check for uniqueness in the sat solver then        
  ClauseId clause_id = d_resolutionProof->registerAssumptionConflict(confl);
  d_conflictMap[conflict] = clause_id;
  d_resolutionProof->endResChain(clause_id);
  Debug("bv-proof") << "BitVectorProof::endBVConflict id"<<clause_id<< " => " << conflict << "\n"; 
}

void BitVectorProof::finalizeConflicts(std::vector<Expr>& conflicts) {
  for(unsigned i = 0; i < conflicts.size(); ++i) {
    Expr confl = conflicts[i];
    Assert (d_conflictMap.find(confl) != d_conflictMap.end());
    ClauseId id = d_conflictMap[confl];
    d_resolutionProof->collectClauses(id);
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
    printBitOf(term, os); 
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

void LFSCBitVectorProof::printBitOf(Expr term, std::ostream& os) {
  Assert (term.getKind() == kind::BITVECTOR_BITOF);
  unsigned bit = term.getOperator().getConst<BitVectorBitOf>().bitIndex;
  Expr var = term[0];
  Assert (var.getKind() == kind::VARIABLE ||
          var.getKind() == kind::SKOLEM); 
  os << "(bitof " << var <<" " << bit <<")"; 
}

void LFSCBitVectorProof::printConstant(Expr term, std::ostream& os) {
  Assert (term.isConst());
  os <<"(a_bv ";
  std::ostringstream paren;
  for (unsigned i = 0; i < utils::getSize(term); ++i) {
    os << "(bvc ";
    os << (utils::getBit(term, i) ? "b1" : "b0") <<" "; 
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
  os <<")" << paren.str();
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
    unsigned low = utils::getExtractLow(term);
    unsigned high = utils::getExtractHigh(term);
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
  std::ostringstream lemma_paren;
  for (unsigned i = 0; i < lemma.size(); ++i) {
    Expr lit = lemma[i];
    if (lit.getKind() == kind::NOT) {
      os << "(intro_assump_t _ _ _ ";
    } else {
      os << "(intro_assump_f _ _ _ ";
    }
    lemma_paren <<")";
    // print corresponding literal in main sat solver
    ProofManager* pm = ProofManager::currentPM(); 
    CnfProof* cnf = pm->getCnfProof(); 
    prop::SatLiteral main_lit = cnf->getLiteral(lit); 
    os << pm->getLitName(main_lit);
    os <<" "; 
    // print corresponding literal in bv sat solver
    prop::SatVariable bb_var = d_cnfProof->getLiteral(lit).getSatVariable();
    os << pm->getAtomName(bb_var, "bb");
    os <<"(\\unit"<<bb_var<<"\n"; 
    lemma_paren <<")";
  }

  Expr lem = utils::mkOr(lemma);
  Assert (d_conflictMap.find(lem) != d_conflictMap.end()); 
  ClauseId lemma_id = d_conflictMap[lem];
  d_resolutionProof->printAssumptionsResolution(lemma_id, os, lemma_paren);
  os <<lemma_paren.str();
  // os << "(clausify_false trust)\n"; 
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
  // print mapping between theory atoms and internal SAT variables
  os << ";; BB atom mapping\n"; 
  d_cnfProof->printAtomMapping(os, paren);

  // print all the bit-blasting clauses marked by finalize conflict
  os << ";; Bit-blasting definitional clauses \n";
  d_cnfProof->printClauses(os, paren);
  os << ";; Bit-blasting learned clauses \n";
  d_resolutionProof->printResolutions(os, paren);
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
