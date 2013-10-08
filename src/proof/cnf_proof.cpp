/*********************                                                        */
/*! \file cnf_proof.cpp
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "proof/cnf_proof.h"
#include "proof/theory_proof.h"
#include "proof/proof_manager.h"
#include "prop/sat_solver_types.h"
#include "prop/minisat/minisat.h"
#include "prop/cnf_stream.h"

using namespace CVC4::prop;

namespace CVC4 {

CnfProof::CnfProof(CnfStream* stream)
  : d_cnfStream(stream)
  , d_theoryProof(NULL)
{}

TheoryProof* CnfProof::getTheoryProof() {
  Assert (d_theoryProof);
  return d_theoryProof; 
}

void CnfProof::setTheoryProof(TheoryProof* theory_proof) {
  Assert (d_theoryProof == NULL);
  d_theoryProof = theory_proof; 
}

void CnfProof::addClause(ClauseId id, const prop::SatClause* clause, ClauseKind kind) {
  for (unsigned i = 0; i < clause->size(); ++i) {
    SatLiteral lit = clause->operator[](i); 
    addVariable(lit.getSatVariable()); 
  }
  if (kind == INPUT) {
    d_inputClauses.insert(std::make_pair(id, clause));
    return;
  }
  Assert (kind == THEORY_LEMMA);
  d_theoryLemmas.insert(std::make_pair(id, clause));
}

void CnfProof::addVariable(prop::SatVariable var) {
  d_propVars.insert(var); 
  Expr atom = getAtom(var); 
  getTheoryProof()->addAtom(atom); 
}

Expr CnfProof::getAtom(prop::SatVariable var) {
  prop::SatLiteral lit (var); 
  Expr atom = d_cnfStream->getNode(lit).toExpr();
  return atom; 
}

CnfProof::~CnfProof() {
  for (IdToClause::iterator it = d_inputClauses.begin(); it != d_inputClauses.end(); ++it) {
    delete it->second; 
  }
  for (IdToClause::iterator it = d_theoryLemmas.begin(); it != d_theoryLemmas.end(); ++it) {
    delete it->second; 
  }
}

void LFSCCnfProof::printAtomMapping(std::ostream& os, std::ostream& paren) {
  for (VarSet::iterator it = d_propVars.begin();it != d_propVars.end();  ++it) {
    Expr atom = getAtom(*it);
    os << "(decl_atom ";
    getTheoryProof()->printFormula(atom, os);
    os << " (\\ " << ProofManager::printVarName(*it) << " (\\ " << ProofManager::printAtomName(*it) << "\n";
    paren << ")))"; 
  }
}

void LFSCCnfProof::printClauses(std::ostream& os, std::ostream& paren) {
  printInputClauses(os, paren); 
  printTheoryLemmas(os, paren);
}

void LFSCCnfProof::printInputClauses(std::ostream& os, std::ostream& paren) {
  os << " ;; Input Clauses \n";  
  for (IdToClause::const_iterator it = d_inputClauses.begin(); it != d_inputClauses.end(); ++it) {
    ClauseId id = it->first;
    const prop::SatClause* clause = it->second;
    os << "(satlem _ _ ";
    std::ostringstream clause_paren; 
    printClause(*clause, os, clause_paren);
    os << " (clausify_false trust)" << clause_paren.str();
    os << "( \\ " << ProofManager::printInputClauseName(id) << "\n"; 
    paren << "))"; 
  }
}


void LFSCCnfProof::printTheoryLemmas(std::ostream& os, std::ostream& paren) {
  os << " ;; Theory Lemmas \n";  
  for (IdToClause::const_iterator it = d_theoryLemmas.begin(); it != d_theoryLemmas.end(); ++it) {
    ClauseId id = it->first;
    const prop::SatClause* clause = it->second;
    os << "(satlem _ _ ";
    std::ostringstream clause_paren; 
    printClause(*clause, os, clause_paren);
    os << " (clausify_false trust)" << clause_paren.str();
    os << "( \\ " << ProofManager::printLemmaClauseName(id) <<"\n"; 
    paren << "))"; 
  }
}

void LFSCCnfProof::printClause(const prop::SatClause& clause, std::ostream& os, std::ostream& paren) {
  for (unsigned i = 0; i < clause.size(); ++i) {
    prop::SatLiteral lit = clause[i];
    prop::SatVariable var = lit.getSatVariable(); 
    if (lit.isNegated()) {
      os << "(ast _ _ _ " << ProofManager::printAtomName(var) <<" (\\ " << ProofManager::printLitName(lit) << " ";
      paren << "))"; 
    } else {
      os << "(asf _ _ _ " << ProofManager::printAtomName(var) <<" (\\ " << ProofManager::printLitName(lit) << " ";
      paren << "))"; 
    }
  }
}


} /* CVC4 namespace */

