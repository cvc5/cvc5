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

void CnfProof::addInputClause(ClauseId id, const ::Minisat::Clause& clause) {
  d_inputClauses.insert(std::make_pair(id, clause)); 
}

void CnfProof::addTheoryLemma(ClauseId id, const ::Minisat::Clause& clause) {
  d_theoryLemmas.insert(std::make_pair(id, clause)); 
}

void CnfProof::addVariable(unsigned var) {
  d_propVars.insert(var); 
  Expr atom = getAtom(var);
  getTheoryProof()->addAtom(atom); 
}

Expr CnfProof::getAtom(unsigned var) {
  Minisat::Lit m_lit = Minisat::mkLit(var); 
  prop::SatLiteral sat_lit = prop::MinisatSatSolver::toSatLiteral(m_lit); 
  Expr atom = d_cnfStream->getNode(sat_lit).toExpr();
  return atom; 
}

void LFSCCnfProof::printAtomMapping(std::ostream& os, std::ostream& paren) {
  for (VarSet::iterator it = d_propVars.begin();it != d_propVars.end();  ++it) {
    Expr atom = getAtom(*it);
    os << "(decl_atom ";
    getTheoryProof()->printFormula(atom, os);
    os << " (\\ " << ProofManager::getVarPrefix() <<*it << " (\\ " << ProofManager::getAtomPrefix() <<*it << "\n";
    paren << ")))"; 
  }
}

void LFSCCnfProof::printClauses(std::ostream& os, std::ostream& paren) {
  printInputClauses(os, paren); 
  printTheoryLemmas(os, paren);
}

void LFSCCnfProof::printInputClauses(std::ostream& os, std::ostream& paren) {
  for (IdToClause::const_iterator it = d_inputClauses.begin(); it != d_inputClauses.end(); ++it) {
    ClauseId id = it->first;
    const Minisat::Clause& clause = it->second;
    os << " ;; input clause \n";  
    os << "(satlem _ _ ";
    std::ostringstream clause_paren; 
    printClause(clause, os, clause_paren);
    os << " (clausify_false trust)" << clause_paren.str();
    os << "( \\ " << ProofManager::getInputClausePrefix() << id <<"\n"; 
    paren << "))"; 
  }
}


void LFSCCnfProof::printTheoryLemmas(std::ostream& os, std::ostream& paren) {
  for (IdToClause::const_iterator it = d_inputClauses.begin(); it != d_inputClauses.end(); ++it) {
    ClauseId id = it->first;
    const Minisat::Clause& clause = it->second;
    os << " ;; theory lemma \n";  
    os << "(satlem _ _ ";
    std::ostringstream clause_paren; 
    printClause(clause, os, clause_paren);
    os << " (clausify_false trust)" << clause_paren.str();
    os << "( \\ " << ProofManager::getLemmaClausePrefix() << id <<"\n"; 
    paren << "))"; 
  }
}

void LFSCCnfProof::printClause(const Minisat::Clause& clause, std::ostream& os, std::ostream& paren) {
  for (int i = 0; i < clause.size(); ++i) {
    Minisat::Lit lit = clause[i];
    unsigned var = Minisat::var(lit);
    if (sign(lit)) {
      os << "(asf _ _ _ " << ProofManager::getAtomPrefix()<< var <<" (\\ " << ProofManager::getLitPrefix() << Minisat::toInt(lit) << " ";
      paren << ")"; 
    } else {
      os << "(ast _ _ _ " << ProofManager::getAtomPrefix()<< var <<" (\\ " << ProofManager::getLitPrefix() << Minisat::toInt(lit) << " ";
      paren << ")"; 
    }
  }
}


} /* CVC4 namespace */

