/*********************                                                        */
/*! \file sat_proof.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Resolution proof
 **
 ** Resolution proof
 **/

#include "cvc4_private.h"

#ifndef __CVC4__SAT__PROOF_IMPLEMENTATION_H
#define __CVC4__SAT__PROOF_IMPLEMENTATION_H

#include "proof/sat_proof.h"
#include "proof/cnf_proof.h"
#include "prop/minisat/minisat.h"
#include "prop/bvminisat/bvminisat.h"
#include "prop/minisat/core/Solver.h"
#include "prop/bvminisat/core/Solver.h"
#include "prop/sat_solver_types.h"

namespace CVC4 {

template <class Solver> 
void printLit (typename Solver::TLit l) {
  Debug("proof:sat") << (sign(l) ? "-" : "") << var(l) + 1;
}

template <class Solver> 
void printClause (typename Solver::TClause& c) {
  for (int i = 0; i < c.size(); i++) {
    Debug("proof:sat") << (sign(c[i]) ? "-" : "") << var(c[i]) + 1 << " ";
  }
}

template <class Solver> 
void printClause (std::vector<typename Solver::TLit>& c) {
  for (unsigned i = 0; i < c.size(); i++) {
    Debug("proof:sat") << (sign(c[i]) ? "-" : "") << var(c[i]) + 1 << " ";
  }
}


template <class Solver> 
void printLitSet(const std::set<typename Solver::TLit>& s) {
  typename std::set < typename Solver::TLit>::const_iterator it = s.begin();
  for(; it != s.end(); ++it) {
    printLit<Solver>(*it);
    Debug("proof:sat") << " ";
  }
  Debug("proof:sat") << std::endl;
}

// purely debugging functions
template <class Solver> 
void printDebug (typename Solver::TLit l) {
  Debug("proof:sat") << (sign(l) ? "-" : "") << var(l) + 1 << std::endl;
}
template <class Solver> 
void printDebug (typename Solver::TClause& c) {
  for (int i = 0; i < c.size(); i++) {
    Debug("proof:sat") << (sign(c[i]) ? "-" : "") << var(c[i]) + 1 << " ";
  }
  Debug("proof:sat") << std::endl;
}


/**
 * Converts the clause associated to id to a set of literals
 *
 * @param id the clause id
 * @param set the clause converted to a set of literals
 */
template <class Solver> 
void TSatProof<Solver>::createLitSet(ClauseId id, LitSet& set) {
  Assert(set.empty());
  if(isUnit(id)) {
    set.insert(getUnit(id));
    return;
  }
  if ( id == d_emptyClauseId) {
    return;
  }
  // if it's an assumption
  if (d_assumptionConflictsDebug.find(id) != d_assumptionConflictsDebug.end()) {
    LitVector* clause = d_assumptionConflictsDebug[id];
    for (unsigned i = 0; i < clause->size(); ++i) {
      set.insert(clause->operator[](i)); 
    }
    return;
  }
  
  typename Solver::TCRef ref = getClauseRef(id);
  typename Solver::TClause& c = getClause(ref);
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
template <class Solver> 
bool resolve(const typename Solver::TLit v,
             std::set<typename Solver::TLit>& clause1,
             std::set<typename Solver::TLit>& clause2, bool s) {
  Assert(!clause1.empty());
  Assert(!clause2.empty());
  typename Solver::TLit var = sign(v) ? ~v : v;
  if (s) {
    // literal appears positive in the first clause
    if( !clause2.count(~var)) {
      if(Debug.isOn("proof:sat")) {
        Debug("proof:sat") << "proof:resolve: Missing literal ";
        printLit<Solver>(var);
        Debug("proof:sat") << std::endl;
      }
      return false;
    }
    clause1.erase(var);
    clause2.erase(~var);
    typename std::set<typename Solver::TLit>::iterator it = clause2.begin(); 
    for (; it!= clause2.end(); ++it) {
      clause1.insert(*it);
    }
  } else {
    // literal appears negative in the first clause
    if( !clause1.count(~var) || !clause2.count(var)) {
      if(Debug.isOn("proof:sat")) {
        Debug("proof:sat") << "proof:resolve: Missing literal ";
        printLit<Solver>(var);
        Debug("proof:sat") << std::endl;
      }
      return false;
    }
    clause1.erase(~var);
    clause2.erase(var);
    typename std::set<typename Solver::TLit>::iterator it = clause2.begin(); 
    for (; it!= clause2.end(); ++it) {
      clause1.insert(*it);
    }
  }
  return true;
}

/// ResChain
template <class Solver> 
ResChain<Solver>::ResChain(ClauseId start) :
    d_start(start),
    d_steps(),
    d_redundantLits(NULL)
  {}
template <class Solver> 
void ResChain<Solver>::addStep(typename Solver::TLit lit, ClauseId id, bool sign) {
  ResStep<Solver> step(lit, id, sign);
  d_steps.push_back(step);
}

template <class Solver> 
void ResChain<Solver>::addRedundantLit(typename Solver::TLit lit) {
  if (d_redundantLits) {
    d_redundantLits->insert(lit);
  } else {
    d_redundantLits = new LitSet();
    d_redundantLits->insert(lit);
  }
}


/// ProxyProof
template <class Solver> 
ProofProxy<Solver>::ProofProxy(TSatProof<Solver>* proof):
  d_proof(proof)
{}

template <class Solver> 
void ProofProxy<Solver>::updateCRef(typename Solver::TCRef oldref, typename Solver::TCRef newref) {
  d_proof->updateCRef(oldref, newref);
}


/// SatProof
 template <class Solver> 
   TSatProof<Solver>::TSatProof(Solver* solver, const std::string& name, bool checkRes) :
   d_solver(solver),
   d_cnfProof(NULL),
   d_idClause(),
   d_clauseId(),
   d_idUnit(),
   d_deleted(),
   d_inputClauses(),
   d_lemmaClauses(),
   d_assumptions(),
   d_assumptionConflicts(),
   d_assumptionConflictsDebug(),
   d_resChains(),
   d_resStack(),
   d_checkRes(checkRes),
   d_emptyClauseId(-1),
   d_nullId(-2),
   d_temp_clauseId(),
   d_temp_idClause(),
   d_unitConflictId(),
   d_storedUnitConflict(false),
   d_name(name),
   d_seenLearnt(),
   d_seenInput(),
   d_seenLemmas() {
   d_proxy = new ProofProxy<Solver>(this);
 }
 
template <class Solver> 
void TSatProof<Solver>::setCnfProof(CnfProof* cnf_proof) {
  Assert (d_cnfProof == NULL);
  d_cnfProof = cnf_proof;
}

// template <class Solver> 
// CnfProof* TSatProof<Solver>::getCnfProof() {
//   Assert (d_cnfProof != NULL);
//   return d_cnfProof;
// }

/**
 * Returns true if the resolution chain corresponding to id
 * does resolve to the clause associated to id
 * @param id
 *
 * @return
 */
template <class Solver> 
bool TSatProof<Solver>::checkResolution(ClauseId id) {
  if(d_checkRes) {
    bool validRes = true;
    Assert(d_resChains.find(id) != d_resChains.end());
    ResChain<Solver>* res = d_resChains[id];
    LitSet clause1;
    createLitSet(res->getStart(), clause1);
    typename ResChain<Solver>::ResSteps& steps = res->getSteps();
    for (unsigned i = 0; i < steps.size(); i++) {
      typename Solver::TLit    var = steps[i].lit;
      LitSet clause2;
      createLitSet (steps[i].id, clause2);
      bool res = resolve<Solver> (var, clause1, clause2, steps[i].sign);
      if(res == false) {
        validRes = false;
        break;
      }
    }
    // compare clause we claimed to prove with the resolution result
    if (isUnit(id)) {
      // special case if it was a unit clause
      typename Solver::TLit unit = getUnit(id);
      validRes = clause1.size() == clause1.count(unit) && !clause1.empty();
      return validRes;
    }
    if (id == d_emptyClauseId) {
      return clause1.empty();
    }
    
    LitVector c;
    getLitVec(id, c); 

    for (unsigned i = 0; i < c.size(); ++i) {
      int count = clause1.erase(c[i]);
      if (count == 0) {
        if(Debug.isOn("proof:sat")) {
          Debug("proof:sat") << "proof:checkResolution::literal not in computed result ";
          printLit<Solver>(c[i]);
          Debug("proof:sat") << "\n";
        }
        validRes = false;
      }
    }
    validRes = clause1.empty();
    if (! validRes) {
      if(Debug.isOn("proof:sat")) {
        Debug("proof:sat") << "proof:checkResolution::Invalid Resolution, unremoved literals: \n";
        printLitSet<Solver>(clause1);
        Debug("proof:sat") << "proof:checkResolution:: result should be: \n";
        printClause<Solver>(c);
      }
    }
    return validRes;

  } else {
    return true;
  }
}




/// helper methods
template <class Solver> 
ClauseId TSatProof<Solver>::getClauseId(typename Solver::TCRef ref) {
  if(d_clauseId.find(ref) == d_clauseId.end()) {
    Debug("proof:sat") << "Missing clause \n";
  }
  Assert(d_clauseId.find(ref) != d_clauseId.end());
  return d_clauseId[ref];
}

template <class Solver> 
ClauseId TSatProof<Solver>::getClauseId(typename Solver::TLit lit) {
  Assert(d_unitId.find(toInt(lit)) != d_unitId.end());
  return d_unitId[toInt(lit)];
}
template <class Solver> 
typename Solver::TCRef TSatProof<Solver>::getClauseRef(ClauseId id) {
  if (d_idClause.find(id) == d_idClause.end()) {
    Debug("proof:sat") << "proof:getClauseRef cannot find clause "<<id<<" "
                       << ((d_deleted.find(id) != d_deleted.end()) ? "deleted" : "")
                       << (isUnit(id)? "Unit" : "") << std::endl;
  }
  Assert(d_idClause.find(id) != d_idClause.end());
  return d_idClause[id];
}

template <class Solver> 
typename Solver::TClause& TSatProof<Solver>::getClause(typename Solver::TCRef ref) {
  Assert(ref != Solver::TCRef_Undef);
  Assert(ref >= 0 && ref < d_solver->ca.size());
  return d_solver->ca[ref];
}

template <class Solver> 
void TSatProof<Solver>::getLitVec(ClauseId id, LitVector& vec) {
  if (isUnit(id)) {
    typename Solver::TLit lit = getUnit(id);
    vec.push_back(lit);
    return; 
  }
  if (isAssumptionConflict(id)) {
    vec = *(d_assumptionConflictsDebug[id]);
    return;
  }
  typename Solver::TCRef cref = getClauseRef(id);
  typename Solver::TClause& cl = getClause(cref);
  for (int i = 0; i < cl.size(); ++i) {
    vec.push_back(cl[i]);
  }
}


template <class Solver> 
typename Solver::TLit TSatProof<Solver>::getUnit(ClauseId id) {
  Assert(d_idUnit.find(id) != d_idUnit.end());
  return d_idUnit[id];
}
template <class Solver> 
bool TSatProof<Solver>::isUnit(ClauseId id) {
  return d_idUnit.find(id) != d_idUnit.end();
}
template <class Solver> 
bool TSatProof<Solver>::isUnit(typename Solver::TLit lit) {
  return d_unitId.find(toInt(lit)) != d_unitId.end();
}
template <class Solver> 
ClauseId TSatProof<Solver>::getUnitId(typename Solver::TLit lit) {
  Assert(isUnit(lit));
  return d_unitId[toInt(lit)];
}
template <class Solver> 
bool TSatProof<Solver>::hasResolution(ClauseId id) {
  return d_resChains.find(id) != d_resChains.end();
}
template <class Solver> 
bool TSatProof<Solver>::isInputClause(ClauseId id) {
  return (d_inputClauses.find(id) != d_inputClauses.end());
}
template <class Solver> 
bool TSatProof<Solver>::isLemmaClause(ClauseId id) {
  return (d_lemmaClauses.find(id) != d_lemmaClauses.end());
}

template <class Solver> 
bool TSatProof<Solver>::isAssumptionConflict(ClauseId id) {
  return d_assumptionConflicts.find(id) != d_assumptionConflicts.end();
}


template <class Solver> 
void TSatProof<Solver>::print(ClauseId id) {
  if (d_deleted.find(id) != d_deleted.end()) {
    Debug("proof:sat") << "del"<<id;
  } else if (isUnit(id)) {
    printLit<Solver>(getUnit(id));
  } else if (id == d_emptyClauseId) {
    Debug("proof:sat") << "empty "<< std::endl;
  }
  else {
    typename Solver::TCRef ref = getClauseRef(id);
    printClause<Solver>(getClause(ref));
  }
}
template <class Solver> 
void TSatProof<Solver>::printRes(ClauseId id) {
  Assert(hasResolution(id));
  Debug("proof:sat") << "id "<< id <<": ";
  printRes(d_resChains[id]);
}
template <class Solver> 
void TSatProof<Solver>::printRes(ResChain<Solver>* res) {
  ClauseId start_id = res->getStart();

  if(Debug.isOn("proof:sat")) {
    Debug("proof:sat") << "(";
    print(start_id);
  }

  typename ResChain<Solver>::ResSteps& steps = res->getSteps();
  for(unsigned i = 0; i < steps.size(); i++ ) {
    typename Solver::TLit v = steps[i].lit;
    ClauseId id = steps[i].id;

    if(Debug.isOn("proof:sat")) {
      Debug("proof:sat") << "[";
      printLit<Solver>(v);
      Debug("proof:sat") << "] ";
      print(id);
    }
  }
  Debug("proof:sat") << ") \n";
}

/// registration methods
template <class Solver> 
  ClauseId TSatProof<Solver>::registerClause(typename Solver::TCRef clause,
					     ClauseKind kind) {
  Assert(clause != Solver::TCRef_Undef);
  typename ClauseIdMap::iterator it = d_clauseId.find(clause);
  if (it == d_clauseId.end()) {
    ClauseId newId = ProofManager::currentPM()->nextId();
    d_clauseId.insert(std::make_pair(clause, newId)); 
    d_idClause.insert(std::make_pair(newId, clause));
    if (kind == INPUT) {
      Assert(d_inputClauses.find(newId) == d_inputClauses.end());
      d_inputClauses.insert(newId));
    }
    if (kind == THEORY_LEMMA) {
      Assert(d_lemmaClauses.find(newId) == d_lemmaClauses.end());
      d_lemmaClauses.insert(newId);
    }
  }
  Debug("proof:sat:detailed") << "registerClause CRef:" << clause << " id:" << d_clauseId[clause] <<  "\n";
  //ProofManager::currentPM()->setRegisteredClauseId( d_clauseId[clause] );
  return d_clauseId[clause];
}
template <class Solver> 
ClauseId TSatProof<Solver>::registerUnitClause(typename Solver::TLit lit,
					       ClauseKind kind) {
  Debug("cores") << "registerUnitClause " << kind << std::endl;
  typename UnitIdMap::iterator it = d_unitId.find(toInt(lit));
  if (it == d_unitId.end()) {
    ClauseId newId = ProofManager::currentPM()->nextId();
    d_unitId.insert(std::make_pair(toInt(lit), newId));
    d_idUnit.insert(std::make_pair(newId, lit));

    if (kind == INPUT) {
      Assert(d_inputClauses.find(newId) == d_inputClauses.end());
      d_inputClauses.insert(newId);
    }
    if (kind == THEORY_LEMMA) {
      Assert(d_lemmaClauses.find(newId) == d_lemmaClauses.end());
      d_lemmaClauses.insert(newId);
    }
  }
  Debug("proof:sat:detailed") << "registerUnitClause " << d_unitId[toInt(lit)] << " " << kind << "\n";
  // ProofManager::currentPM()->setRegisteredClauseId( d_unitId[toInt(lit)] );
  return d_unitId[toInt(lit)];
}
template <class Solver> 
void TSatProof<Solver>::registerAssumption(const typename Solver::TVar var) {
  Assert (d_assumptions.find(var) == d_assumptions.end());
  d_assumptions.insert(var);
}

template <class Solver> 
ClauseId TSatProof<Solver>::registerAssumptionConflict(const typename Solver::TLitVec& confl) {
  // Uniqueness is checked in the bit-vector proof
  // should be vars
  for (int i = 0; i < confl.size(); ++i) {
    Assert (d_assumptions.find(var(confl[i])) != d_assumptions.end());
  }
  ClauseId new_id = d_idCounter++;
  d_assumptionConflicts.insert(new_id);
  LitVector* vec_confl = new LitVector(confl.size()); 
  for (int i = 0; i < confl.size(); ++i) {
    vec_confl->operator[](i) = confl[i];
  }
  d_assumptionConflictsDebug[new_id] = vec_confl;
  return new_id;
}


template <class Solver> 
void TSatProof<Solver>::removedDfs(typename Solver::TLit lit, LitSet* removedSet, LitVector& removeStack, LitSet& inClause, LitSet& seen) {
  // if we already added the literal return
  if (seen.count(lit)) {
    return;
  }

  typename Solver::TCRef reason_ref = d_solver->reason(var(lit));
  if (reason_ref == Solver::TCRef_Undef) {
    seen.insert(lit);
    removeStack.push_back(lit);
    return;
  }

  int size = getClause(reason_ref).size();
  for (int i = 1; i < size; i++ ) {
    typename Solver::TLit v = getClause(reason_ref)[i];
    if(inClause.count(v) == 0 && seen.count(v) == 0) {
      removedDfs(v, removedSet, removeStack, inClause, seen);
    }
  }
  if(seen.count(lit) == 0) {
    seen.insert(lit);
    removeStack.push_back(lit);
  }
}

template <class Solver> 
void TSatProof<Solver>::removeRedundantFromRes(ResChain<Solver>* res, ClauseId id) {
  LitSet* removed = res->getRedundant();
  if (removed == NULL) {
    return;
  }

  LitSet inClause;
  createLitSet(id, inClause);

  LitVector removeStack;
  LitSet seen;
  for (typename LitSet::iterator it = removed->begin(); it != removed->end(); ++it) {
    removedDfs(*it, removed, removeStack, inClause, seen);
  }

  for (int i = removeStack.size()-1; i >= 0; --i) {
    typename Solver::TLit lit = removeStack[i];
    typename Solver::TCRef reason_ref = d_solver->reason(var(lit));
    ClauseId reason_id;

    if (reason_ref == Solver::TCRef_Undef) {
      Assert(isUnit(~lit));
      reason_id = getUnitId(~lit);
    } else {
      reason_id = registerClause(reason_ref, LEARNT, uint64_t(-1));
    }
    res->addStep(lit, reason_id, !sign(lit));
  }
  removed->clear();
}
 
template <class Solver> 
void TSatProof<Solver>::registerResolution(ClauseId id, ResChain<Solver>* res) {
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
template <class Solver> 
void TSatProof<Solver>::startResChain(typename Solver::TCRef start) {
  ClauseId id = getClauseId(start);
  ResChain<Solver>* res = new ResChain<Solver>(id);
  d_resStack.push_back(res);
}

template <class Solver> 
void TSatProof<Solver>::startResChain(typename Solver::TLit start) {
  ClauseId id = getUnitId(start);
  ResChain<Solver>* res = new ResChain<Solver>(id);
  d_resStack.push_back(res);
}


template <class Solver> 
void TSatProof<Solver>::addResolutionStep(typename Solver::TLit lit,
                                          typename Solver::TCRef clause, bool sign) {
  ClauseId id = registerClause(clause, LEARNT, uint64_t(-1));
  ResChain<Solver>* res = d_resStack.back();
  res->addStep(lit, id, sign);
}

template <class Solver> 
void TSatProof<Solver>::endResChain(ClauseId id) {
  Assert(d_resStack.size() > 0);
  ResChain<Solver>* res = d_resStack.back();
  registerResolution(id, res);
  d_resStack.pop_back();
}


template <class Solver> 
void TSatProof<Solver>::endResChain(typename Solver::TCRef clause) {
  Assert(d_resStack.size() > 0);
  ClauseId id = registerClause(clause, LEARNT, uint64_t(-1));
  ResChain<Solver>* res = d_resStack.back();
  registerResolution(id, res);
  d_resStack.pop_back();
}

template <class Solver> 
void TSatProof<Solver>::endResChain(typename Solver::TLit lit) {
  Assert(d_resStack.size() > 0);
  ClauseId id = registerUnitClause(lit, LEARNT, uint64_t(-1));
  ResChain<Solver>* res = d_resStack.back();
  registerResolution(id, res);
  d_resStack.pop_back();
}


template <class Solver> 
void TSatProof<Solver>::cancelResChain() {
  Assert(d_resStack.size() > 0);
  d_resStack.pop_back();
}


template <class Solver> 
void TSatProof<Solver>::storeLitRedundant(typename Solver::TLit lit) {
  Assert(d_resStack.size() > 0);
  ResChain<Solver>* res = d_resStack.back();
  res->addRedundantLit(lit);
}

/// constructing resolutions
template <class Solver> 
void TSatProof<Solver>::resolveOutUnit(typename Solver::TLit lit) {
  ClauseId id = resolveUnit(~lit);
  ResChain<Solver>* res = d_resStack.back();
  res->addStep(lit, id, !sign(lit));
}
template <class Solver> 
void TSatProof<Solver>::storeUnitResolution(typename Solver::TLit lit) {
  Debug("cores") << "STORE UNIT RESOLUTION" << std::endl;
  resolveUnit(lit);
}
template <class Solver> 
ClauseId TSatProof<Solver>::resolveUnit(typename Solver::TLit lit) {
  // first check if we already have a resolution for lit
  if(isUnit(lit)) {
    ClauseId id = getClauseId(lit);
    Assert(hasResolution(id) || isInputClause(id) || isLemmaClause(id));
    return id;
  }
  typename Solver::TCRef reason_ref = d_solver->reason(var(lit));
  Assert(reason_ref != Solver::TCRef_Undef);

  ClauseId reason_id = registerClause(reason_ref, LEARNT);

  ResChain<Solver>* res = new ResChain<Solver>(reason_id);
  // Here, the call to resolveUnit() can reallocate memory in the
  // clause allocator.  So reload reason ptr each time.
  typename Solver::TClause* reason = &getClause(reason_ref);
  for (int i = 0;
       i < reason->size();
       i++, reason = &getClause(reason_ref)) {
    typename Solver::TLit l = (*reason)[i];
    if(lit != l) {
      ClauseId res_id = resolveUnit(~l);
      res->addStep(l, res_id, !sign(l));
    }
  }
  ClauseId unit_id = registerUnitClause(lit, LEARNT, uint64_t(-1));
  registerResolution(unit_id, res);
  return unit_id;
}
template <class Solver> 
void TSatProof<Solver>::toStream(std::ostream& out) {
  Debug("proof:sat") << "TSatProof<Solver>::printProof\n";
  Unimplemented("native proof printing not supported yet");
}
template <class Solver> 
ClauseId TSatProof<Solver>::storeUnitConflict(typename Solver::TLit conflict_lit,
                                              ClauseKind kind) {
  Debug("cores") << "STORE UNIT CONFLICT" << std::endl;
  Assert(!d_storedUnitConflict);
  d_unitConflictId = registerUnitClause(conflict_lit, kind);
  d_storedUnitConflict = true;
  Debug("proof:sat:detailed") <<"storeUnitConflict " << d_unitConflictId << "\n";
  return d_storedUnitConflict;
}
template <class Solver> 
void TSatProof<Solver>::finalizeProof(typename Solver::TCRef conflict_ref) {
  Assert(d_resStack.size() == 0);
  Assert(conflict_ref != Solver::TCRef_Undef);
  ClauseId conflict_id;
  if (conflict_ref == Solver::TCRef_Lazy) {
    Assert(d_storedUnitConflict);
    conflict_id = d_unitConflictId;

    ResChain<Solver>* res = new ResChain<Solver>(conflict_id);
    typename Solver::TLit lit = d_idUnit[conflict_id];
    ClauseId res_id = resolveUnit(~lit);
    res->addStep(lit, res_id, !sign(lit));

    registerResolution(d_emptyClauseId, res);

    return;
  } else {
    Assert(!d_storedUnitConflict);
    conflict_id = registerClause(conflict_ref, LEARNT); //FIXME
  }

  if(Debug.isOn("proof:sat")) {
    Debug("proof:sat") << "proof::finalizeProof Final Conflict ";
    print(conflict_id);
  }

  ResChain<Solver>* res = new ResChain<Solver>(conflict_id);
  // Here, the call to resolveUnit() can reallocate memory in the
  // clause allocator.  So reload conflict ptr each time.
  typename Solver::TClause* conflict = &getClause(conflict_ref);
  for (int i = 0;
       i < conflict->size();
       ++i, conflict = &getClause(conflict_ref)) {
    typename Solver::TLit lit = (*conflict)[i];
    ClauseId res_id = resolveUnit(~lit);
    res->addStep(lit, res_id, !sign(lit));
  }
  registerResolution(d_emptyClauseId, res);
}

/// CRef manager
template <class Solver> 
void TSatProof<Solver>::updateCRef(typename Solver::TCRef oldref,
                                   typename Solver::TCRef newref) {
  if (d_clauseId.find(oldref) == d_clauseId.end()) {
    return;
  }
  ClauseId id = getClauseId(oldref);
  Assert(d_temp_clauseId.find(newref) == d_temp_clauseId.end());
  Assert(d_temp_idClause.find(id) == d_temp_idClause.end());
  d_temp_clauseId[newref] = id;
  d_temp_idClause[id] = newref;
}
template <class Solver> 
void TSatProof<Solver>::finishUpdateCRef() {
  d_clauseId.swap(d_temp_clauseId);
  d_temp_clauseId.clear();

  d_idClause.swap(d_temp_idClause);
  d_temp_idClause.clear();
}
template <class Solver> 
void TSatProof<Solver>::markDeleted(typename Solver::TCRef clause) {
  if (d_clauseId.find(clause) != d_clauseId.end()) {
    ClauseId id = getClauseId(clause);
    Assert(d_deleted.find(id) == d_deleted.end());
    d_deleted.insert(id);
    if (isLemmaClause(id)) {
      const typename Solver::TClause& minisat_cl = getClause(clause);
      prop::SatClause* sat_cl = new prop::SatClause();
      toSatClause<Solver>(minisat_cl, *sat_cl);
      d_deletedTheoryLemmas.insert(std::make_pair(id, sat_cl));
    }
  }
}

// template<>
// void toSatClause< ::BVMinisat::Solver> (const BVMinisat::Solver::TClause& minisat_cl,
//                                         prop::SatClause& sat_cl) {
  
//   prop::BVMinisatSatSolver::toSatClause(minisat_cl, sat_cl);
// }



template <class Solver> 
void TSatProof<Solver>::constructProof(ClauseId conflict) {
  collectClauses(conflict);
}

template <class Solver> 
std::string TSatProof<Solver>::clauseName(ClauseId id) {
  std::ostringstream os;
  if (isInputClause(id)) {
    os << ProofManager::getInputClauseName(id, d_name);
    return os.str();
  } else
  if (isLemmaClause(id)) {
    os << ProofManager::getLemmaClauseName(id, d_name);
    return os.str();
  }else {
    os << ProofManager::getLearntClauseName(id, d_name);
    return os.str();
  }
}

// template <class Solver> 
// void TSatProof<Solver>::addToProofManager(ClauseId id, ClauseKind kind) {
//   if (isUnit(id)) {
//     typename Solver::TLit lit = getUnit(id);
//     prop::SatLiteral sat_lit = toSatLiteral<Solver>(lit);
//     prop::SatClause* clause = new prop::SatClause();
//     clause->push_back(sat_lit);
//     ProofManager::currentPM()->addTheoryLemma(id, clause, kind);
//     return;
//   }

//   if (isDeleted(id)) {
//     Assert(kind == THEORY_LEMMA);
//     prop::SatClause* clause = d_deletedTheoryLemmas.find(id)->second;
//     ProofManager::currentPM()->addTheoryLemma(id, clause, kind);
//     return;
//   }

//   typename Solver::TCRef ref = getClauseRef(id);
//   const typename Solver::TClause& minisat_cl = getClause(ref);
//   prop::SatClause* clause = new prop::SatClause();
//   toSatClause<Solver>(minisat_cl, *clause);
//   ProofManager::currentPM()->addTheoryLemma(id, clause, kind);
// }

// template<class Solver>
// void TSatProof<Solver>::addToCnfProof(ClauseId id) {
//   if (isUnit(id)) {
//     typename Solver::TLit lit = getUnit(id);
//     prop::SatLiteral sat_lit = toSatLiteral<Solver>(lit);
//     prop::SatClause* clause = new prop::SatClause();
//     clause->push_back(sat_lit);
//     d_cnfProof->addInputClause(id, clause);
//     return;
//   }

//   Assert (!isDeleted(id)); 

//   typename Solver::TCRef ref = getClauseRef(id);
//   const typename Solver::TClause& minisat_cl = getClause(ref);
//   prop::SatClause* clause = new prop::SatClause();
//   toSatClause<Solver>(minisat_cl, *clause);
//   d_cnfProof->addInputClause(id, clause);
// }


template <class Solver> 
void TSatProof<Solver>::collectClauses(ClauseId id) {
  if (d_seenInputsLemmas.find(id) != d_seenInputsLemmas.end()) {
    return;
  }

  if (isInputClause(id) ||
      isLemmaClause(id)) {
    d_seenInputsLemmas.insert(id);
    return;
  } else if (!isAssumptionConflict(id)) {
    d_seenLearnt.insert(id);
  }

  Assert(d_resChains.find(id) != d_resChains.end());
  ResChain<Solver>* res = d_resChains[id];
  ClauseId start = res->getStart();
  collectClauses(start);

  typename ResChain<Solver>::ResSteps steps = res->getSteps();
  for(size_t i = 0; i < steps.size(); i++) {
    collectClauses(steps[i].id);
  }
}

/// LFSCSatProof class
template <class Solver> 
void LFSCSatProof<Solver>::printResolution(ClauseId id, std::ostream& out, std::ostream& paren) {
  out << "(satlem_simplify _ _ _ ";

  ResChain<Solver>* res = this->d_resChains[id];
  typename ResChain<Solver>::ResSteps& steps = res->getSteps();

  for (int i = steps.size()-1; i >= 0; i--) {
    out << "(";
    out << (steps[i].sign? "R" : "Q") << " _ _ ";
  }

  ClauseId start_id = res->getStart();
  // WHY DID WE NEED THIS?
  // if(isInputClause(start_id)) {
  //   d_seenInput.insert(start_id);
  // }
  out << this->clauseName(start_id) << " ";

  for(unsigned i = 0; i < steps.size(); i++) {
    prop::SatVariable v = prop::MinisatSatSolver::toSatVariable(var(steps[i].lit));
    out << this->clauseName(steps[i].id) << " "<<ProofManager::getVarName(v, this->d_name) <<")";
  }

  if (id == this->d_emptyClauseId) {
    out <<"(\\empty empty)";
    return;
  }

  out << "(\\" << this->clauseName(id) << "\n";   // bind to lemma name
  paren << "))";                            // closing parethesis for lemma binding and satlem
}

/// LFSCSatProof class
template <class Solver> 
void LFSCSatProof<Solver>::printAssumptionsResolution(ClauseId id, std::ostream& out, std::ostream& paren) {
  Assert (this->isAssumptionConflict(id));
  // print the resolution proving the assumption conflict
  printResolution(id, out, paren);
  // resolve out assumptions to prove empty clause
  out << "(satlem_simplify _ _ _ ";
  std::vector<typename Solver::TLit>& confl = *(this->d_assumptionConflictsDebug[id]);
  
  Assert (confl.size());

  for (unsigned i = 0; i < confl.size(); ++i) {
    prop::SatLiteral lit = toSatLiteral<Solver>(confl[i]);
    out <<"(";
    out << (lit.isNegated() ? "Q" : "R") <<" _ _ ";
  }
  
  out << this->clauseName(id)<< " "; 
  for (int i = confl.size() - 1; i >= 0; --i) {
    prop::SatLiteral lit = toSatLiteral<Solver>(confl[i]);
    prop::SatVariable v = lit.getSatVariable();
    out << "unit"<< v <<" ";
    out << ProofManager::getVarName(v, this->d_name) <<")";
  }
  out <<"(\\ e e)\n";
  paren <<")";
}


template <class Solver>
void LFSCSatProof<Solver>::printResolutions(std::ostream& out, std::ostream& paren) {
  std::set<ClauseId>::iterator it = this->d_seenLearnt.begin();
  for(; it!= this->d_seenLearnt.end(); ++it) {
    if(*it != this->d_emptyClauseId) {
      printResolution(*it, out, paren);
    }
  }
}

template <class Solver>
void LFSCSatProof<Solver>::printResolutionEmptyClause(std::ostream& out, std::ostream& paren) {
  printResolution(this->d_emptyClauseId, out, paren);  
}

}/* CVC4 namespace */


#endif /* __CVC4__SAT__PROOF_IMPLEMENTATION_H */
