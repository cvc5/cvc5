/*********************                                                        */
/*! \file sat_proof.cpp
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters
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

#include "proof/sat_proof.h"
#include "proof/proof_manager.h"
#include "prop/minisat/core/Solver.h"
#include "prop/minisat/minisat.h"

using namespace std;
using namespace Minisat;
using namespace CVC4::prop;
namespace CVC4 {

/// some helper functions

void printLit (Minisat::Lit l) {
  Debug("proof:sat") << (sign(l) ? "-" : "") << var(l) + 1;
}

void printClause (Minisat::Clause& c) {
  for (int i = 0; i < c.size(); i++) {
    Debug("proof:sat") << (sign(c[i]) ? "-" : "") << var(c[i]) + 1 << " ";
  }
}

void printLitSet(const LitSet& s) {
  for(LitSet::iterator it = s.begin(); it != s.end(); ++it) {
    printLit(*it);
    Debug("proof:sat") << " ";
  }
  Debug("proof:sat") << endl;
}

// purely debugging functions
void printDebug (Minisat::Lit l) {
  Debug("proof:sat") << (sign(l) ? "-" : "") << var(l) + 1 << endl;
}

void printDebug (Minisat::Clause& c) {
  for (int i = 0; i < c.size(); i++) {
    Debug("proof:sat") << (sign(c[i]) ? "-" : "") << var(c[i]) + 1 << " ";
  }
  Debug("proof:sat") << endl;
}


int SatProof::d_idCounter = 0;

/**
 * Converts the clause associated to id to a set of literals
 *
 * @param id the clause id
 * @param set the clause converted to a set of literals
 */
void SatProof::createLitSet(ClauseId id, LitSet& set) {
  Assert(set.empty());
  if(isUnit(id)) {
    set.insert(getUnit(id));
    return;
  }
  if ( id == d_emptyClauseId) {
    return;
  }
  CRef ref = getClauseRef(id);
  Clause& c = getClause(ref);
  for (int i = 0; i < c.size(); i++) {
    set.insert(c[i]);
  }
}


/**
 * Resolves clause1 and clause2 on variable var and stores the
 * result in clause1
 * @param v
 * @param clause1
 * @param clause2
 */
bool resolve(const Lit v, LitSet& clause1, LitSet& clause2, bool s) {
  Assert(!clause1.empty());
  Assert(!clause2.empty());
  Lit var = sign(v) ? ~v : v;
  if (s) {
    // literal appears positive in the first clause
    if( !clause2.count(~var)) {
      if(Debug.isOn("proof:sat")) {
        Debug("proof:sat") << "proof:resolve: Missing literal ";
        printLit(var);
        Debug("proof:sat") << endl;
      }
      return false;
    }
    clause1.erase(var);
    clause2.erase(~var);
    for (LitSet::iterator it = clause2.begin(); it!= clause2.end(); ++it) {
      clause1.insert(*it);
    }
  } else {
    // literal appears negative in the first clause
    if( !clause1.count(~var) || !clause2.count(var)) {
      if(Debug.isOn("proof:sat")) {
        Debug("proof:sat") << "proof:resolve: Missing literal ";
        printLit(var);
        Debug("proof:sat") << endl;
      }
      return false;
    }
    clause1.erase(~var);
    clause2.erase(var);
    for (LitSet::iterator it = clause2.begin(); it!= clause2.end(); ++it) {
      clause1.insert(*it);
    }
  }
  return true;
}

/// ResChain

ResChain::ResChain(ClauseId start) :
    d_start(start),
    d_steps(),
    d_redundantLits(NULL)
  {}

void ResChain::addStep(Lit lit, ClauseId id, bool sign) {
  ResStep step(lit, id, sign);
  d_steps.push_back(step);
}


void ResChain::addRedundantLit(Lit lit) {
  if (d_redundantLits) {
    d_redundantLits->insert(lit);
  } else {
    d_redundantLits = new LitSet();
    d_redundantLits->insert(lit);
  }
}


/// ProxyProof

ProofProxy::ProofProxy(SatProof* proof):
  d_proof(proof)
{}

void ProofProxy::updateCRef(CRef oldref, CRef newref) {
  d_proof->updateCRef(oldref, newref);
}


/// SatProof

SatProof::SatProof(Minisat::Solver* solver, bool checkRes) :
    d_solver(solver),
    d_idClause(),
    d_clauseId(),
    d_idUnit(),
    d_deleted(),
    d_inputClauses(),
    d_lemmaClauses(),
    d_resChains(),
    d_resStack(),
    d_checkRes(checkRes),
    d_emptyClauseId(-1),
    d_nullId(-2),
    d_temp_clauseId(),
    d_temp_idClause(),
    d_unitConflictId(),
    d_storedUnitConflict(false),
    d_seenLearnt(),
    d_seenInput(),
    d_seenLemmas()
  {
    d_proxy = new ProofProxy(this);
  }

/**
 * Returns true if the resolution chain corresponding to id
 * does resolve to the clause associated to id
 * @param id
 *
 * @return
 */
bool SatProof::checkResolution(ClauseId id) {
  if(d_checkRes) {
    bool validRes = true;
    Assert(d_resChains.find(id) != d_resChains.end());
    ResChain* res = d_resChains[id];
    LitSet clause1;
    createLitSet(res->getStart(), clause1);
    ResSteps& steps = res->getSteps();
    for (unsigned i = 0; i < steps.size(); i++) {
      Lit    var = steps[i].lit;
      LitSet clause2;
      createLitSet (steps[i].id, clause2);
      bool res = resolve (var, clause1, clause2, steps[i].sign);
      if(res == false) {
        validRes = false;
        break;
      }
    }
    // compare clause we claimed to prove with the resolution result
    if (isUnit(id)) {
      // special case if it was a unit clause
      Lit unit = getUnit(id);
      validRes = clause1.size() == clause1.count(unit) && !clause1.empty();
      return validRes;
    }
    if (id == d_emptyClauseId) {
      return clause1.empty();
    }
    CRef ref = getClauseRef(id);
    Clause& c = getClause(ref);
    for (int i = 0; i < c.size(); ++i) {
      int count = clause1.erase(c[i]);
      if (count == 0) {
        if(Debug.isOn("proof:sat")) {
          Debug("proof:sat") << "proof:checkResolution::literal not in computed result ";
          printLit(c[i]);
          Debug("proof:sat") << "\n";
        }
        validRes = false;
      }
    }
    validRes = clause1.empty();
    if (! validRes) {
      if(Debug.isOn("proof:sat")) {
        Debug("proof:sat") << "proof:checkResolution::Invalid Resolution, unremoved literals: \n";
        printLitSet(clause1);
        Debug("proof:sat") << "proof:checkResolution:: result should be: \n";
        printClause(c);
      }
    }
    return validRes;

  } else {
    return true;
  }
}




/// helper methods

ClauseId SatProof::getClauseId(::Minisat::CRef ref) {
  if(d_clauseId.find(ref) == d_clauseId.end()) {
    Debug("proof:sat") << "Missing clause \n";
  }
  Assert(d_clauseId.find(ref) != d_clauseId.end());
  return d_clauseId[ref];
}


ClauseId SatProof::getClauseId(::Minisat::Lit lit) {
  Assert(d_unitId.find(toInt(lit)) != d_unitId.end());
  return d_unitId[toInt(lit)];
}

Minisat::CRef SatProof::getClauseRef(ClauseId id) {
  if (d_idClause.find(id) == d_idClause.end()) {
    Debug("proof:sat") << "proof:getClauseRef cannot find clause "<<id<<" "
                       << ((d_deleted.find(id) != d_deleted.end()) ? "deleted" : "")
                       << (isUnit(id)? "Unit" : "") << endl;
  }
  Assert(d_idClause.find(id) != d_idClause.end());
  return d_idClause[id];
}

Clause& SatProof::getClause(CRef ref) {
  Assert(ref != CRef_Undef);
  Assert(ref >= 0 && ref < d_solver->ca.size());
  return d_solver->ca[ref];
}

Minisat::Lit SatProof::getUnit(ClauseId id) {
  Assert(d_idUnit.find(id) != d_idUnit.end());
  return d_idUnit[id];
}

bool SatProof::isUnit(ClauseId id) {
  return d_idUnit.find(id) != d_idUnit.end();
}

bool SatProof::isUnit(::Minisat::Lit lit) {
  return d_unitId.find(toInt(lit)) != d_unitId.end();
}

ClauseId SatProof::getUnitId(::Minisat::Lit lit) {
  Assert(isUnit(lit));
  return d_unitId[toInt(lit)];
}

bool SatProof::hasResolution(ClauseId id) {
  return d_resChains.find(id) != d_resChains.end();
}

bool SatProof::isInputClause(ClauseId id) {
  return (d_inputClauses.find(id) != d_inputClauses.end());
}

bool SatProof::isLemmaClause(ClauseId id) {
  return (d_lemmaClauses.find(id) != d_lemmaClauses.end());
}


void SatProof::print(ClauseId id) {
  if (d_deleted.find(id) != d_deleted.end()) {
    Debug("proof:sat") << "del"<<id;
  } else if (isUnit(id)) {
    printLit(getUnit(id));
  } else if (id == d_emptyClauseId) {
    Debug("proof:sat") << "empty "<< endl;
  }
  else {
    CRef ref = getClauseRef(id);
    printClause(getClause(ref));
  }
}

void SatProof::printRes(ClauseId id) {
  Assert(hasResolution(id));
  Debug("proof:sat") << "id "<< id <<": ";
  printRes(d_resChains[id]);
}

void SatProof::printRes(ResChain* res) {
  ClauseId start_id = res->getStart();

  if(Debug.isOn("proof:sat")) {
    Debug("proof:sat") << "(";
    print(start_id);
  }

  ResSteps& steps = res->getSteps();
  for(unsigned i = 0; i < steps.size(); i++ ) {
    Lit v = steps[i].lit;
    ClauseId id = steps[i].id;

    if(Debug.isOn("proof:sat")) {
      Debug("proof:sat") << "[";
      printLit(v);
      Debug("proof:sat") << "] ";
      print(id);
    }
  }
  Debug("proof:sat") << ") \n";
}

/// registration methods

ClauseId SatProof::registerClause(::Minisat::CRef clause, ClauseKind kind) {
  Assert(clause != CRef_Undef);
  ClauseIdMap::iterator it = d_clauseId.find(clause);
  if (it == d_clauseId.end()) {
    ClauseId newId = d_idCounter++;
    d_clauseId[clause] = newId;
    d_idClause[newId] = clause;
    if (kind == INPUT) {
      Assert(d_inputClauses.find(newId) == d_inputClauses.end());
      d_inputClauses.insert(newId);
    }
    if (kind == THEORY_LEMMA) {
      Assert(d_lemmaClauses.find(newId) == d_lemmaClauses.end());
      d_lemmaClauses.insert(newId);
    }
  }
  Debug("proof:sat:detailed") <<"registerClause CRef:" << clause <<" id:" << d_clauseId[clause] << " " << kind << "\n";
  return d_clauseId[clause];
}

ClauseId SatProof::registerUnitClause(::Minisat::Lit lit, ClauseKind kind) {
  UnitIdMap::iterator it = d_unitId.find(toInt(lit));
  if (it == d_unitId.end()) {
    ClauseId newId = d_idCounter++;
    d_unitId[toInt(lit)] = newId;
    d_idUnit[newId] = lit;
    if (kind == INPUT) {
      Assert(d_inputClauses.find(newId) == d_inputClauses.end());
      d_inputClauses.insert(newId);
    }
    if (kind == THEORY_LEMMA) {
      Assert(d_lemmaClauses.find(newId) == d_lemmaClauses.end());
      d_lemmaClauses.insert(newId);
    }
  }
  Debug("proof:sat:detailed") <<"registerUnitClause " << d_unitId[toInt(lit)] << " " << kind <<"\n";
  return d_unitId[toInt(lit)];
}

void SatProof::removedDfs(::Minisat::Lit lit, LitSet* removedSet, LitVector& removeStack, LitSet& inClause, LitSet& seen) {
  // if we already added the literal return
  if (seen.count(lit)) {
    return;
  }

  CRef reason_ref = d_solver->reason(var(lit));
  if (reason_ref == CRef_Undef) {
    seen.insert(lit);
    removeStack.push_back(lit);
    return;
  }

  int size = getClause(reason_ref).size();
  for (int i = 1; i < size; i++ ) {
    Lit v = getClause(reason_ref)[i];
    if(inClause.count(v) == 0 && seen.count(v) == 0) {
      removedDfs(v, removedSet, removeStack, inClause, seen);
    }
  }
  if(seen.count(lit) == 0) {
    seen.insert(lit);
    removeStack.push_back(lit);
  }
}


void SatProof::removeRedundantFromRes(ResChain* res, ClauseId id) {
  LitSet* removed = res->getRedundant();
  if (removed == NULL) {
    return;
  }

  LitSet inClause;
  createLitSet(id, inClause);

  LitVector removeStack;
  LitSet seen;
  for (LitSet::iterator it = removed->begin(); it != removed->end(); ++it) {
    removedDfs(*it, removed, removeStack, inClause, seen);
  }

  for (int i = removeStack.size()-1; i >= 0; --i) {
    Lit lit = removeStack[i];
    CRef reason_ref = d_solver->reason(var(lit));
    ClauseId reason_id;

    if (reason_ref == CRef_Undef) {
      Assert(isUnit(~lit));
      reason_id = getUnitId(~lit);
    } else {
      reason_id = registerClause(reason_ref);
    }
    res->addStep(lit, reason_id, !sign(lit));
  }
  removed->clear();
}

void SatProof::registerResolution(ClauseId id, ResChain* res) {
  Assert(res != NULL);

  removeRedundantFromRes(res, id);
  Assert(res->redundantRemoved());

  d_resChains[id] = res;
  if(Debug.isOn("proof:sat")) {
    printRes(id);
  }
  if(d_checkRes) {
    Assert(checkResolution(id));
  }
}


/// recording resolutions

void SatProof::startResChain(::Minisat::CRef start) {
  ClauseId id = getClauseId(start);
  ResChain* res = new ResChain(id);
  d_resStack.push_back(res);
}

void SatProof::addResolutionStep(::Minisat::Lit lit, ::Minisat::CRef clause, bool sign) {
  ClauseId id = registerClause(clause);
  ResChain* res = d_resStack.back();
  res->addStep(lit, id, sign);
}

void SatProof::endResChain(CRef clause) {
  Assert(d_resStack.size() > 0);
  ClauseId id = registerClause(clause);
  ResChain* res = d_resStack.back();
  registerResolution(id, res);
  d_resStack.pop_back();
}


void SatProof::endResChain(::Minisat::Lit lit) {
  Assert(d_resStack.size() > 0);
  ClauseId id = registerUnitClause(lit);
  ResChain* res = d_resStack.back();
  registerResolution(id, res);
  d_resStack.pop_back();
}

void SatProof::storeLitRedundant(::Minisat::Lit lit) {
  Assert(d_resStack.size() > 0);
  ResChain* res = d_resStack.back();
  res->addRedundantLit(lit);
}

/// constructing resolutions

void SatProof::resolveOutUnit(::Minisat::Lit lit) {
  ClauseId id = resolveUnit(~lit);
  ResChain* res = d_resStack.back();
  res->addStep(lit, id, !sign(lit));
}

void SatProof::storeUnitResolution(::Minisat::Lit lit) {
  resolveUnit(lit);
}

ClauseId SatProof::resolveUnit(::Minisat::Lit lit) {
  // first check if we already have a resolution for lit
  if(isUnit(lit)) {
    ClauseId id = getClauseId(lit);
    Assert(hasResolution(id) || isInputClause(id) || isLemmaClause(id));
    return id;
  }
  CRef reason_ref = d_solver->reason(var(lit));
  Assert(reason_ref != CRef_Undef);

  ClauseId reason_id = registerClause(reason_ref);

  ResChain* res = new ResChain(reason_id);
  // Here, the call to resolveUnit() can reallocate memory in the
  // clause allocator.  So reload reason ptr each time.
  Clause* reason = &getClause(reason_ref);
  for (int i = 0;
       i < reason->size();
       i++, reason = &getClause(reason_ref)) {
    Lit l = (*reason)[i];
    if(lit != l) {
      ClauseId res_id = resolveUnit(~l);
      res->addStep(l, res_id, !sign(l));
    }
  }
  ClauseId unit_id = registerUnitClause(lit);
  registerResolution(unit_id, res);
  return unit_id;
}

void SatProof::toStream(std::ostream& out) {
  Debug("proof:sat") << "SatProof::printProof\n";
  Unimplemented("native proof printing not supported yet");
}

void SatProof::storeUnitConflict(::Minisat::Lit conflict_lit, ClauseKind kind) {
  Assert(!d_storedUnitConflict);
  d_unitConflictId = registerUnitClause(conflict_lit, kind);
  d_storedUnitConflict = true;
  Debug("proof:sat:detailed") <<"storeUnitConflict " << d_unitConflictId << "\n";
}

void SatProof::finalizeProof(::Minisat::CRef conflict_ref) {
  Assert(d_resStack.size() == 0);
  Assert(conflict_ref != ::Minisat::CRef_Undef);
  ClauseId conflict_id;
  if (conflict_ref == ::Minisat::CRef_Lazy) {
    Assert(d_storedUnitConflict);
    conflict_id = d_unitConflictId;

    ResChain* res = new ResChain(conflict_id);
    Lit lit = d_idUnit[conflict_id];
    ClauseId res_id = resolveUnit(~lit);
    res->addStep(lit, res_id, !sign(lit));

    registerResolution(d_emptyClauseId, res);

    return;
  } else {
    Assert(!d_storedUnitConflict);
    conflict_id = registerClause(conflict_ref); //FIXME
  }

  if(Debug.isOn("proof:sat")) {
    Debug("proof:sat") << "proof::finalizeProof Final Conflict ";
    print(conflict_id);
  }

  ResChain* res = new ResChain(conflict_id);
  // Here, the call to resolveUnit() can reallocate memory in the
  // clause allocator.  So reload conflict ptr each time.
  Clause* conflict = &getClause(conflict_ref);
  for (int i = 0;
       i < conflict->size();
       ++i, conflict = &getClause(conflict_ref)) {
    Lit lit = (*conflict)[i];
    ClauseId res_id = resolveUnit(~lit);
    res->addStep(lit, res_id, !sign(lit));
  }
  registerResolution(d_emptyClauseId, res);
}

/// CRef manager

void SatProof::updateCRef(::Minisat::CRef oldref, ::Minisat::CRef newref) {
  if (d_clauseId.find(oldref) == d_clauseId.end()) {
    return;
  }
  ClauseId id = getClauseId(oldref);
  Assert(d_temp_clauseId.find(newref) == d_temp_clauseId.end());
  Assert(d_temp_idClause.find(id) == d_temp_idClause.end());
  d_temp_clauseId[newref] = id;
  d_temp_idClause[id] = newref;
}

void SatProof::finishUpdateCRef() {
  d_clauseId.swap(d_temp_clauseId);
  d_temp_clauseId.clear();

  d_idClause.swap(d_temp_idClause);
  d_temp_idClause.clear();
}

void SatProof::markDeleted(CRef clause) {
  if (d_clauseId.find(clause) != d_clauseId.end()) {
    ClauseId id = getClauseId(clause);
    Assert(d_deleted.find(id) == d_deleted.end());
    d_deleted.insert(id);
    if (isLemmaClause(id)) {
      const Clause& minisat_cl = getClause(clause);
      SatClause* sat_cl = new SatClause();
      MinisatSatSolver::toSatClause(minisat_cl, *sat_cl);
      d_deletedTheoryLemmas.insert(std::make_pair(id, sat_cl));
    }
  }
}

void SatProof::constructProof() {
  collectClauses(d_emptyClauseId);
}

std::string SatProof::clauseName(ClauseId id) {
  ostringstream os;
  if (isInputClause(id)) {
    os << ProofManager::getInputClauseName(id);
    return os.str();
  } else
  if (isLemmaClause(id)) {
    os << ProofManager::getLemmaClauseName(id);
    return os.str();
  }else {
    os << ProofManager::getLearntClauseName(id);
    return os.str();
  }
}

void SatProof::addToProofManager(ClauseId id, ClauseKind kind) {
  if (isUnit(id)) {
    Minisat::Lit lit = getUnit(id);
    prop::SatLiteral sat_lit = MinisatSatSolver::toSatLiteral(lit);
    prop::SatClause* clause = new SatClause();
    clause->push_back(sat_lit);
    ProofManager::currentPM()->addClause(id, clause, kind);
    return;
  }

  if (isDeleted(id)) {
    Assert(kind == THEORY_LEMMA);
    SatClause* clause = d_deletedTheoryLemmas.find(id)->second;
    ProofManager::currentPM()->addClause(id, clause, kind);
    return;
  }

  CRef ref = getClauseRef(id);
  const Clause& minisat_cl = getClause(ref);
  SatClause* clause = new SatClause();
  MinisatSatSolver::toSatClause(minisat_cl, *clause);
  ProofManager::currentPM()->addClause(id, clause, kind);
}

void SatProof::collectClauses(ClauseId id) {
  if (d_seenLearnt.find(id) != d_seenLearnt.end()) {
    return;
  }
  if (d_seenInput.find(id) != d_seenInput.end()) {
    return;
  }
  if (d_seenLemmas.find(id) != d_seenLemmas.end()) {
    return;
  }

  if (isInputClause(id)) {
    addToProofManager(id, INPUT);
    d_seenInput.insert(id);
    return;
  } else if (isLemmaClause(id)) {
    addToProofManager(id, THEORY_LEMMA);
    d_seenLemmas.insert(id);
    return;
  } else {
    d_seenLearnt.insert(id);
  }

  Assert(d_resChains.find(id) != d_resChains.end());
  ResChain* res = d_resChains[id];
  ClauseId start = res->getStart();
  collectClauses(start);

  ResSteps steps = res->getSteps();
  for(size_t i = 0; i < steps.size(); i++) {
    collectClauses(steps[i].id);
  }
}

/// LFSCSatProof class

void LFSCSatProof::printResolution(ClauseId id, std::ostream& out, std::ostream& paren) {
  out << "(satlem_simplify _ _ _ ";

  ResChain* res = d_resChains[id];
  ResSteps& steps = res->getSteps();

  for (int i = steps.size()-1; i >= 0; i--) {
    out << "(";
    out << (steps[i].sign? "R" : "Q") << " _ _ ";

  }

  ClauseId start_id = res->getStart();
  // WHY DID WE NEED THIS?
  // if(isInputClause(start_id)) {
  //   d_seenInput.insert(start_id);
  // }
  out << clauseName(start_id) << " ";

  for(unsigned i = 0; i < steps.size(); i++) {
    out << clauseName(steps[i].id) << " "<<ProofManager::getVarName(MinisatSatSolver::toSatVariable(var(steps[i].lit))) <<")";
  }

  if (id == d_emptyClauseId) {
    out <<"(\\empty empty)";
    return;
  }

  out << "(\\" << clauseName(id) << "\n";   // bind to lemma name
  paren << "))";                            // closing parethesis for lemma binding and satlem
}

void LFSCSatProof::printResolutions(std::ostream& out, std::ostream& paren) {
  for(IdSet::iterator it = d_seenLearnt.begin(); it!= d_seenLearnt.end(); ++it) {
    if(*it != d_emptyClauseId) {
      printResolution(*it, out, paren);
    }
  }
  printResolution(d_emptyClauseId, out, paren);
}


} /* CVC4 namespace */

