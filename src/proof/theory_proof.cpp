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
#include "proof/proof_utils.h"
#include "prop/sat_solver_types.h"

using namespace CVC4;
using namespace CVC4::theory;

TheoryProofEngine::TheoryProofEngine()
  : d_registrationCache()
  , d_theoryProofTable()
{
  d_theoryProofTable[theory::THEORY_BOOL] = new LFSCBooleanProof(this);
}

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
    return;
  }

  if (id == THEORY_BV) {
    d_theoryProofTable[id] = new LFSCBitVectorProof((bv::TheoryBV*)th, this);
    return;
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
  if (theory_id == THEORY_BUILTIN ||
      term.getKind() == kind::ITE) {
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
  if (pm->getLogic() == "ALL_SUPPORTED") return theory::THEORY_BV;
  Unreachable();
}

void LFSCTheoryProofEngine::printTerm(Expr term, std::ostream& os) {
  TheoryId theory_id = Theory::theoryOf(term);
  // boolean terms and ITEs are special because they
  // are common to all theories
  if (theory_id == THEORY_BUILTIN ||
      term.getKind() == kind::ITE ||
      term.getKind() == kind::EQUAL) {
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

  // BitVector theory is special case: must know all
  // conflicts needed ahead of time for resolution
  // proof lemmas
  std::vector<Expr> bv_lemmas;
  for (; it != end; ++it) {
    ClauseId id = it->first;
    TheoryId theory_id = getTheoryForLemma(id);
    if (theory_id != THEORY_BV) continue;

    const prop::SatClause* clause = it->second;
    std::vector<Expr> conflict;
    for(unsigned i = 0; i < clause->size(); ++i) {
      prop::SatLiteral lit = (*clause)[i];
      Expr atom = pm->getCnfProof()->getAtom(lit.getSatVariable());
      if (atom.isConst()) {
        Assert (atom == utils::mkTrue());
        continue;
      }
      Expr expr_lit = lit.isNegated() ? atom.notExpr() : atom;
      conflict.push_back(expr_lit);
    }
    bv_lemmas.push_back(utils::mkSortedExpr(kind::OR, conflict));
  }
  // FIXME: ugly, move into bit-vector proof by adding lemma
  // queue inside each theory_proof
  BitVectorProof* bv = ProofManager::getBitVectorProof(); 
  bv->finalizeConflicts(bv_lemmas); 
  bv->printBitblasting(os, paren);
  
  it = pm->begin_lemmas();
  
  for (; it != end; ++it) {
    ClauseId id = it->first;
    const prop::SatClause* clause = it->second;
    // printing clause as it appears in resolution proof
    os << "(satlem _ _ ";
    std::ostringstream clause_paren;
    ProofManager::currentPM()->getCnfProof()->printClause(*clause, os, clause_paren);
    
    std::vector<Expr> clause_expr;
    for(unsigned i = 0; i < clause->size(); ++i) {
      prop::SatLiteral lit = (*clause)[i];
      Expr atom = pm->getCnfProof()->getAtom(lit.getSatVariable());
      if (atom.isConst()) {
        Assert (atom == utils::mkTrue());
        continue;
      }
      Expr expr_lit = lit.isNegated() ? atom.notExpr(): atom;
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

void LFSCTheoryProofEngine::printCoreTerm(Expr term, std::ostream& os) {
  if (term.isVariable()) {
    os << term;
    return;
  }

  Kind k = term.getKind(); 
  switch(k) {
  case kind::ITE:
    os << (term.getType().isBoolean() ? "(ifte ": "(ite _ ");
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
    printSort(term[0].getType(), os);
    printTerm(term[0], os);
    os << " ";
    printTerm(term[1], os);
    os << "))";
    Assert (term.getNumChildren() == 2); 
    return;

  case kind::CHAIN: {
    // LFSC doesn't allow declarations with variable numbers of
    // arguments, so we have to flatten chained operators, like =.
    Kind op = term.getOperator().getConst<Chain>().getOperator();
    size_t n = term.getNumChildren();
    std::ostringstream paren;
    for(size_t i = 1; i < n; ++i) {
      if(i + 1 < n) {
        os << "(" << utils::toLFSCCoreKind(kind::AND) << " ";
        paren << ")";
      }
      os << "(" << utils::toLFSCCoreKind(op) << " ";
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

BooleanProof::BooleanProof(TheoryProofEngine* proofEngine)
  : TheoryProof(NULL, proofEngine)
{}

void BooleanProof::registerTerm(Expr term) {
  Assert (term.getType().isBoolean());
  
  if (term.isVariable() && d_declarations.find(term) == d_declarations.end()) {
    d_declarations.insert(term);
    return;
  }
  for (unsigned i = 0; i < term.getNumChildren(); ++i) {
    d_proofEngine->registerTerm(term[i]);
  }
}

void LFSCBooleanProof::printTerm(Expr term, std::ostream& os) {
  Assert (term.getType().isBoolean());
  if (term.isVariable()) {
    os << "(p_app " << term <<")";
    return;
  }

  Kind k = term.getKind(); 
  switch(k) {
  case kind::OR:
  case kind::AND:
  case kind::XOR:
  case kind::IFF:
  case kind::IMPLIES:
  case kind::NOT:
    // print the Boolean operators
    os << "(" << utils::toLFSCCoreKind(k);
    if(term.getNumChildren() > 2) {
      // LFSC doesn't allow declarations with variable numbers of
      // arguments, so we have to flatten these N-ary versions.
      std::ostringstream paren;
      os << " ";
      for (unsigned i = 0; i < term.getNumChildren(); ++i) {
        d_proofEngine->printTerm(term[i], os);
        os << " ";
        if(i < term.getNumChildren() - 2) {
          os << "(" << utils::toLFSCCoreKind(k) << " ";
          paren << ")";
        }
      }
      os << paren.str() << ")";
    } else {
      // this is for binary and unary operators
      for (unsigned i = 0; i < term.getNumChildren(); ++i) {
        os << " ";
        d_proofEngine->printTerm(term[i], os);
      }
      os << ")";
    }
    return;

  case kind::CONST_BOOLEAN:
    os << (term.getConst<bool>() ? "true" : "false");
    return;

  default:
    Unhandled(k);
  }

}
void LFSCBooleanProof::printSort(Type type, std::ostream& os) {
  Assert (type.isBoolean());
  os << "Bool";
}
void LFSCBooleanProof::printDeclarations(std::ostream& os, std::ostream& paren) {
  for (ExprSet::const_iterator it = d_declarations.begin(); it != d_declarations.end(); ++it) {
    Expr term = *it;
    
    os << "(% " << term << " (term ";
    printSort(term.getType(), os);
    os <<")\n";
    paren <<")";
  }
}



