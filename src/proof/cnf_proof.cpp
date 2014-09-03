/*********************                                                        */
/*! \file cnf_proof.cpp
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

#include "proof/cnf_proof.h"
#include "proof/theory_proof.h"
#include "proof/proof_manager.h"
#include "prop/sat_solver_types.h"
#include "prop/minisat/minisat.h"
#include "prop/cnf_stream.h"

using namespace CVC4::prop;

namespace CVC4 {

CnfProof::CnfProof(CnfStream* stream, const std::string& name)
  : d_cnfStream(stream)
  , d_atomToSatVar()
  , d_satVarToAtom()
  , d_inputClauses()
  , d_name(name)
{}


Expr CnfProof::getAtom(prop::SatVariable var) {
  prop::SatLiteral lit (var);
  Node node = d_cnfStream->getNode(lit);
  Expr atom = node.toExpr();
  return atom;
}

prop::SatLiteral CnfProof::getLiteral(Expr expr) {
  Assert(d_cnfStream->hasLiteral(expr));
  return d_cnfStream->getLiteral(Node::fromExpr(expr)); 
}

void CnfProof::addInputClause(ClauseId id, const prop::SatClause* clause) {
  Assert (d_inputClauses.find(id) == d_inputClauses.end());
  d_inputClauses[id] = clause;
  for (unsigned i = 0; i < clause->size(); ++i) {
    SatLiteral lit = clause->operator[](i);
    SatVariable var = lit.getSatVariable();
    Expr atom = getAtom(var);
    if (d_satVarToAtom.find(var) == d_satVarToAtom.end()) {
      Assert (d_atomToSatVar.find(atom) == d_atomToSatVar.end());
      d_satVarToAtom[var] = atom;
      d_atomToSatVar[atom] = var;
    }
  }
}

CnfProof::~CnfProof() {
  IdToClause::iterator it = d_inputClauses.begin();
  IdToClause::iterator end = d_inputClauses.end();
  for (; it != end; ++it) {
    delete it->second;
  }
}

void LFSCCnfProof::printAtomMapping(std::ostream& os, std::ostream& paren) {
  atom_iterator it = begin_atoms(); 
  atom_iterator end = end_atoms(); 

  for (;it != end;  ++it) {
    os << "(decl_atom ";
    prop::SatVariable var = it->second;
    Expr atom = it->first;
    //FIXME hideous
    LFSCTheoryProofEngine* pe = (LFSCTheoryProofEngine*)ProofManager::currentPM()->getTheoryProofEngine();
    pe->printTerm(atom, os);
    
    os << " (\\ " << ProofManager::getVarName(var, d_name) << " (\\ " << ProofManager::getAtomName(var, d_name) << "\n";
    paren << ")))";
  }
}

void LFSCCnfProof::printClauses(std::ostream& os, std::ostream& paren) {
  printInputClauses(os, paren);
}

void LFSCCnfProof::printInputClauses(std::ostream& os, std::ostream& paren) {
  os << " ;; Input Clauses \n";
  clause_iterator it = begin_input_clauses();
  clause_iterator end = end_input_clauses();

  for (; it != end; ++it) {
    ClauseId id = it->first;
    const prop::SatClause* clause = it->second;
    os << "(satlem _ _ ";
    std::ostringstream clause_paren;
    printClause(*clause, os, clause_paren);
    os << " (clausify_false trust)" << clause_paren.str();
    os << "( \\ " << ProofManager::getInputClauseName(id, d_name) << "\n";
    paren << "))";
  }
}

void LFSCCnfProof::printClause(const prop::SatClause& clause, std::ostream& os, std::ostream& paren) {
  for (unsigned i = 0; i < clause.size(); ++i) {
    prop::SatLiteral lit = clause[i];
    prop::SatVariable var = lit.getSatVariable();
    if (lit.isNegated()) {
      os << "(ast _ _ _ " << ProofManager::getAtomName(var, d_name) <<" (\\ " << ProofManager::getLitName(lit, d_name) << " ";
      paren << "))";
    } else {
      os << "(asf _ _ _ " << ProofManager::getAtomName(var, d_name) <<" (\\ " << ProofManager::getLitName(lit, d_name) << " ";
      paren << "))";
    }
  }
}

} /* CVC4 namespace */
