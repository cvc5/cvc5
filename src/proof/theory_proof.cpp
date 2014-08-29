/*********************                                                        */
/*! \file theory_proof.cpp
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: Morgan Deters
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

#include "proof/theory_proof.h"
#include "proof/proof_manager.h"
#include "theory/theory.h"
#include "proof/uf_proof.h"
#include "proof/array_proof.h"
#include "proof/bitvector_proof.h"
#include "proof/cnf_proof.h"
#include "prop/sat_solver_types.h"

using namespace CVC4;
using namespace CVC4::theory;

TheoryProofEngine::TheoryProofEngine()
  : d_registrationCache()
{}

TheoryProofEngine::~TheoryProofEngine() {
  TheoryProofTable::iterator it = d_theoryProofTable.begin();
  TheoryProofTable::iterator end = d_theoryProofTable.end();
  for (; it != end; ++it) {
    delete it->second; 
  }
}


void TheoryProofEngine::registerTheory(theory::Theory* th) {
  TheoryId id = th->getId();
  Assert (d_theoryProofTable.find(id) == d_theoryProofTable.end());
  
  if (id == THEORY_UF) {
    d_theoryProofTable[id] = new LFSCUFProof((uf::TheoryUF*)th, this);
  }

  if (id == THEORY_BV) {
    d_theoryProofTable[id] = new LFSCBitVectorProof((bv::TheoryBV*)th, this);
  }
  // TODO Arrays and other theories
}

TheoryProof* TheoryProofEngine::getTheoryProof(TheoryId id) {
  Assert (d_theoryProofTable.find(id) != d_theoryProofTable.end());
  return d_theoryProofTable[id];
}

void TheoryProofEngine::registerTerm(Expr term) {
  if (d_registrationCache.count(term)) {
    return;
  }
  
  TheoryId theory_id = Theory::theoryOf(term);

  // don't need to register boolean terms 
  if (theory_id == THEORY_BOOL) {
    for (unsigned i = 0; i < term.getNumChildren(); ++i) {
      registerTerm(term[i]); 
    }
    d_registrationCache.insert(term);
    return;
  }
  
  getTheoryProof(theory_id)->registerTerm(term);
  d_registrationCache.insert(term);
}

theory::TheoryId TheoryProofEngine::getTheoryForLemma(ClauseId id) {
  // TODO: have proper dispatch here
  ProofManager* pm = ProofManager::currentPM(); 
  
  if (pm->getLogic() == "QF_UF") return theory::THEORY_UF;
  if (pm->getLogic() == "QF_BV") return theory::THEORY_BV;
  Unreachable(); 
}

void LFSCTheoryProofEngine::printTerm(Expr term, std::ostream& os) {
  TheoryId theory_id = Theory::theoryOf(term);
  // boolean terms and ITEs are special because they
  // are common to all theories
  if (theory_id == THEORY_BOOL ||
      theory_id == THEORY_BUILTIN ||
      term.getKind() == kind::ITE ||
      term.getKind() == kind::EQUAL ||
      term.getKind() == kind::VARIABLE ||
      term.getKind() == kind::SKOLEM) {
    printCoreTerm(term, os);
    return;
  }
  // dispatch to proper theory
  getTheoryProof(theory_id)->printTerm(term, os);
}

void LFSCTheoryProofEngine::printSort(Type type, std::ostream& os) {
  if (type.isSort()) {
    getTheoryProof(THEORY_UF)->printSort(type, os);
    return; 
  }
  if (type.isBitVector()) {
    getTheoryProof(THEORY_BV)->printSort(type, os);
    return; 
  }
  
  if (type.isArray()) {
    getTheoryProof(THEORY_ARRAY)->printSort(type, os);
    return; 
  }
  Unreachable(); 
}

void LFSCTheoryProofEngine::printAssertions(std::ostream& os, std::ostream& paren) {
  unsigned counter = 0;
  ProofManager::assertions_iterator it = ProofManager::currentPM()->begin_assertions();
  ProofManager::assertions_iterator end = ProofManager::currentPM()->end_assertions();

  // collect declarations first
  for(; it != end; ++it) {
    registerTerm(*it);
  }
  printDeclarations(os, paren);

  it = ProofManager::currentPM()->begin_assertions();
  for (; it != end; ++it) {
    os << "(% A" << counter++ << " (th_holds ";
    printTerm(*it,  os);
    os << ")\n";
    paren << ")";
  }
}

void LFSCTheoryProofEngine::printDeclarations(std::ostream& os, std::ostream& paren) {
  TheoryProofTable::const_iterator it = d_theoryProofTable.begin();
  TheoryProofTable::const_iterator end = d_theoryProofTable.end();
  for (; it != end; ++it) {
    it->second->printDeclarations(os, paren);
  }
}

void LFSCTheoryProofEngine::printTheoryLemmas(std::ostream& os, std::ostream& paren) {
  os << " ;; Theory Lemmas \n";
  ProofManager* pm = ProofManager::currentPM();
  ProofManager::clause_iterator it = pm->begin_lemmas();
  ProofManager::clause_iterator end = pm->end_lemmas();

  for (; it != end; ++it) {
    ClauseId id = it->first;
    const prop::SatClause* clause = it->second;
    // printing clause as it appears in resolution proof
    os << "(satlem _ _ ";
    std::ostringstream clause_paren;
    LFSCCnfProof::printClause(*clause, os, clause_paren);
    
    std::vector<Expr> clause_expr;
    for(unsigned i = 0; i < clause->size(); ++i) {
      prop::SatLiteral lit = (*clause)[i];
      Expr atom = pm->getCnfProof()->getAtom(lit.getSatVariable());
      Expr expr_lit = lit.isNegated() ? atom.notExpr() :  atom;
      clause_expr.push_back(expr_lit);
    }
    
    // query appropriate theory for proof of clause
    TheoryId theory_id = getTheoryForLemma(id);
    getTheoryProof(theory_id)->printTheoryLemmaProof(clause_expr, os, paren); 
    // os << " (clausify_false trust)";
    os << clause_paren.str();
    os << "( \\ " << ProofManager::getLemmaClauseName(id) <<"\n";
    paren << "))";
  }
}


std::string toLFSCCoreKind(Kind kind) {
  switch(kind) {
  case kind::OR : return "or";
  case kind::AND: return "and";
  case kind::XOR: return "xor";
  case kind::EQUAL: return "=";
  case kind::IFF: return "iff";
  case kind::IMPLIES: return "impl";
  case kind::NOT: return "not";
  default:
    Unreachable();
  }
}

void LFSCTheoryProofEngine::printCoreTerm(Expr term, std::ostream& os) {
  if (term.isVariable()) {
    if (term.getType().isBoolean()) {
      os << "(p_app" << term <<")";
    } else {
      os << term; 
    }
    return;
  }

  Kind k = term.getKind(); 
  switch(k) {
  case kind::ITE:
    os << (term.getType().isBoolean() ? "(ifte " : "(ite _ ");
    printTerm(term[0], os);
    os << " ";
    printTerm(term[1], os);
    os << " ";
    printTerm(term[2], os);
    os << ")";
    return;

  case kind::EQUAL:
    os << "(";
    os << "= ";
    printSort(term[0].getType(), os);
    printTerm(term[0], os);
    os << " ";
    printTerm(term[1], os);
    os << ")";
    return;

  case kind::DISTINCT:
    os << "(not (= ";
    os << term[0].getType() << " ";
    printTerm(term[0], os);
    os << " ";
    printTerm(term[1], os);
    os << "))";
    return;

  case kind::OR:
  case kind::AND:
  case kind::XOR:
  case kind::IFF:
  case kind::IMPLIES:
  case kind::NOT:
    // print the Boolean operators
    os << "(" << toLFSCCoreKind(k);
    if(term.getNumChildren() > 2) {
      // LFSC doesn't allow declarations with variable numbers of
      // arguments, so we have to flatten these N-ary versions.
      std::ostringstream paren;
      os << " ";
      for (unsigned i = 0; i < term.getNumChildren(); ++i) {
        printTerm(term[i], os);
        os << " ";
        if(i < term.getNumChildren() - 2) {
          os << "(" << toLFSCCoreKind(k) << " ";
          paren << ")";
        }
      }
      os << paren.str() << ")";
    } else {
      // this is for binary and unary operators
      for (unsigned i = 0; i < term.getNumChildren(); ++i) {
        os << " ";
        printTerm(term[i], os);
      }
      os << ")";
    }
    return;

  case kind::CONST_BOOLEAN:
    os << (term.getConst<bool>() ? "true" : "false");
    return;

  case kind::CHAIN: {
    // LFSC doesn't allow declarations with variable numbers of
    // arguments, so we have to flatten chained operators, like =.
    Kind op = term.getOperator().getConst<Chain>().getOperator();
    size_t n = term.getNumChildren();
    std::ostringstream paren;
    for(size_t i = 1; i < n; ++i) {
      if(i + 1 < n) {
        os << "(" << toLFSCCoreKind(kind::AND) << " ";
        paren << ")";
      }
      os << "(" << toLFSCCoreKind(op) << " ";
      printTerm(term[i - 1], os);
      os << " ";
      printTerm(term[i], os);
      os << ")";
      if(i + 1 < n) {
        os << " ";
      }
    }
    os << paren.str();
    return;
  }

  default:
    Unhandled(k);
  }
 
}
