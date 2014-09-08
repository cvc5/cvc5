/*********************                                                        */
/*! \file proof_manager.cpp
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

#include "proof/proof_manager.h"
#include "util/proof.h"
#include "proof/sat_proof_implementation.h"
#include "proof/cnf_proof.h"
#include "proof/theory_proof.h"
#include "util/cvc4_assert.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"

namespace CVC4 {

std::string append(const std::string& str, uint64_t num) {
  std::ostringstream os;
  os << str << num;
  return os.str();
}

ProofManager::ProofManager(ProofFormat format)
  : d_satProof(NULL)
  , d_cnfProof(NULL)
  , d_theoryProof(NULL)
  , d_theoryLemmas()
  , d_inputFormulas()
  , d_fullProof(NULL)
  , d_format(format)
{}

ProofManager::~ProofManager() {
  delete d_satProof;
  delete d_cnfProof;
  delete d_theoryProof;
  delete d_fullProof;

  // for(IdToClause::iterator it = d_inputClauses.begin();
  //     it != d_inputClauses.end();
  //     ++it) {
  //   delete it->second;
  // }

  for(IdToClause::iterator it = d_theoryLemmas.begin();
      it != d_theoryLemmas.end();
      ++it) {
    delete it->second;
  }

  // FIXME: memory leak because there are deleted theory lemmas that
  // were not used in the SatProof
}

ProofManager* ProofManager::currentPM() {
  return smt::currentProofManager();
}

Proof* ProofManager::getProof(SmtEngine* smt) {
  if (currentPM()->d_fullProof != NULL) {
    return currentPM()->d_fullProof;
  }
  Assert (currentPM()->d_format == LFSC);

  currentPM()->d_fullProof = new LFSCProof(smt,
                                           (LFSCCoreSatProof*)getSatProof(),
                                           (LFSCCnfProof*)getCnfProof(),
                                           (LFSCTheoryProofEngine*)getTheoryProofEngine());
  return currentPM()->d_fullProof;
}

CoreSatProof* ProofManager::getSatProof() {
  Assert (currentPM()->d_satProof);
  return currentPM()->d_satProof;
}

CnfProof* ProofManager::getCnfProof() {
  Assert (currentPM()->d_cnfProof);
  return currentPM()->d_cnfProof;
}

TheoryProofEngine* ProofManager::getTheoryProofEngine() {
  Assert (currentPM()->d_theoryProof);
  return currentPM()->d_theoryProof;
}

UFProof* ProofManager::getUfProof() {
  TheoryProof* pf = getTheoryProofEngine()->getTheoryProof(theory::THEORY_UF);
  return (UFProof*)pf; 
}
BitVectorProof* ProofManager::getBitVectorProof() {
  TheoryProof* pf = getTheoryProofEngine()->getTheoryProof(theory::THEORY_BV);
  return (BitVectorProof*)pf; 
}

ArrayProof* ProofManager::getArrayProof() {
  TheoryProof* pf = getTheoryProofEngine()->getTheoryProof(theory::THEORY_ARRAY);
  return (ArrayProof*)pf; 
}

void ProofManager::initSatProof(Minisat::Solver* solver) {
  Assert (currentPM()->d_satProof == NULL);
  Assert(currentPM()->d_format == LFSC);
  currentPM()->d_satProof = new LFSCCoreSatProof(solver, "");
}

void ProofManager::initCnfProof(prop::CnfStream* cnfStream) {
  ProofManager* pm = currentPM();
  Assert (pm->d_cnfProof == NULL);
  Assert (pm->d_format == LFSC);
  CnfProof* cnf = new LFSCCnfProof(cnfStream, "");
  pm->d_cnfProof = cnf;
  Assert(pm-> d_satProof != NULL);
  pm->d_satProof->setCnfProof(cnf); 
}

void ProofManager::initTheoryProofEngine() {
  Assert (currentPM()->d_theoryProof == NULL);
  Assert (currentPM()->d_format == LFSC);
  currentPM()->d_theoryProof = new LFSCTheoryProofEngine();
}


std::string ProofManager::getInputClauseName(ClauseId id,
                                             const std::string& prefix) {
  return append(prefix+".pb", id);
}
std::string ProofManager::getLemmaClauseName(ClauseId id,
                                             const std::string& prefix) {
  return append(prefix+".lem", id);
}
std::string ProofManager::getLearntClauseName(ClauseId id,
                                              const std::string& prefix) {
  return append(prefix+".cl", id);
}
std::string ProofManager::getVarName(prop::SatVariable var,
                                     const std::string& prefix) {
  return append(prefix+".v", var);
}
std::string ProofManager::getAtomName(prop::SatVariable var,
                                      const std::string& prefix) {
  return append(prefix+".a", var);
}
std::string ProofManager::getLitName(prop::SatLiteral lit,
                                     const std::string& prefix) {
  return append(prefix+".l", lit.toInt());
}

void ProofManager::addTheoryLemma(ClauseId id, const prop::SatClause* clause) {
  Assert (d_theoryLemmas.find(id) == d_theoryLemmas.end()); 
  d_theoryLemmas.insert(std::make_pair(id, clause));
  d_cnfProof->collectAtoms(clause);
}

void ProofManager::addAssertion(Expr formula) {
  d_inputFormulas.insert(formula);
}

// void ProofManager::registerTheoryAtom(Expr atom, prop::SatVariable var) {
//   Assert (d_satVarToAtom.find(var) == d_satVarToAtom.end() &&
//           d_atomToSatVar.find(atom) == d_atomToSatVar.end());
//   d_satVarToAtom[var] = atom;
//   d_atomToSatVar[atom] = var; 
// }

void ProofManager::setLogic(const std::string& logic_string) {
  d_logic = logic_string;
}


LFSCProof::LFSCProof(SmtEngine* smtEngine, LFSCCoreSatProof* sat, LFSCCnfProof* cnf, LFSCTheoryProofEngine* theory)
  : d_cnfProof(cnf)
  , d_satProof(sat)
  , d_theoryProof(theory)
  , d_smtEngine(smtEngine)
{
  d_satProof->constructProof();
}

void LFSCProof::toStream(std::ostream& out) {
  smt::SmtScope scope(d_smtEngine);
  std::ostringstream paren;
  out << "(check\n";
  if (d_theoryProof == NULL) {
    d_theoryProof = new LFSCTheoryProofEngine();
  }

  // declare the theory atoms

  CnfProof::atom_iterator begin = d_cnfProof->begin_atoms();
  CnfProof::atom_iterator end = d_cnfProof->end_atoms();
  for(CnfProof::atom_iterator it = begin; it != end; ++it) {
    d_theoryProof->registerTerm(it->first);
  }
  // print out the assertions
  d_theoryProof->printAssertions(out, paren);
  out << "(: (holds cln)\n";
  // print mapping between theory atoms and internal SAT variables
  d_cnfProof->printAtomMapping(out, paren);
  // print input clauses in resolution proof
  d_cnfProof->printClauses(out, paren);
  // print theory lemmas for resolution proof
  d_theoryProof->printTheoryLemmas(out, paren);
  // priunt actual resolution proof
  d_satProof->printResolutions(out, paren);
  d_satProof->printResolutionEmptyClause(out, paren);
  paren <<")))\n;;";
  out << paren.str();
  out << "\n";
}


} /* CVC4  namespace */
