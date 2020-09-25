/*********************                                                        */
/*! \file sat_proof_implementation.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Tim King, Guy Katz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Resolution proof
 **
 ** Resolution proof
 **/

#include "cvc4_private.h"

#ifndef CVC4__SAT__PROOF_IMPLEMENTATION_H
#define CVC4__SAT__PROOF_IMPLEMENTATION_H

#include "proof/clause_id.h"
#include "proof/sat_proof.h"
#include "prop/minisat/core/Solver.h"
#include "prop/minisat/minisat.h"
#include "prop/sat_solver_types.h"
#include "smt/smt_statistics_registry.h"

namespace CVC4 {

template <class Solver>
void printLit(typename Solver::TLit l) {
  Debug("proof:sat") << (sign(l) ? "-" : "") << var(l) + 1;
}

template <class Solver>
void printClause(const typename Solver::TClause& c) {
  for (int i = 0; i < c.size(); i++) {
    Debug("proof:sat") << (sign(c[i]) ? "-" : "") << var(c[i]) + 1 << " ";
  }
}

template <class Solver>
void printClause(const std::vector<typename Solver::TLit>& c) {
  for (unsigned i = 0; i < c.size(); i++) {
    Debug("proof:sat") << (sign(c[i]) ? "-" : "") << var(c[i]) + 1 << " ";
  }
}

template <class Solver>
void printLitSet(const std::set<typename Solver::TLit>& s) {
  typename std::set<typename Solver::TLit>::const_iterator it = s.begin();
  for (; it != s.end(); ++it) {
    printLit<Solver>(*it);
    Debug("proof:sat") << " ";
  }
  Debug("proof:sat") << std::endl;
}

// purely debugging functions
template <class Solver>
void printDebug(typename Solver::TLit l) {
  Debug("proof:sat") << (sign(l) ? "-" : "") << var(l) + 1 << std::endl;
}
template <class Solver>
void printDebug(typename Solver::TClause& c) {
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
  if (isUnit(id)) {
    set.insert(getUnit(id));
    return;
  }
  if (id == d_emptyClauseId) {
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
  const typename Solver::TClause& c = getClause(ref);
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
    if (!clause2.count(~var)) {
      if (Debug.isOn("proof:sat")) {
        Debug("proof:sat") << "proof:resolve: Missing literal ";
        printLit<Solver>(var);
        Debug("proof:sat") << std::endl;
      }
      return false;
    }
    clause1.erase(var);
    clause2.erase(~var);
    typename std::set<typename Solver::TLit>::iterator it = clause2.begin();
    for (; it != clause2.end(); ++it) {
      clause1.insert(*it);
    }
  } else {
    // literal appears negative in the first clause
    if (!clause1.count(~var) || !clause2.count(var)) {
      if (Debug.isOn("proof:sat")) {
        Debug("proof:sat") << "proof:resolve: Missing literal ";
        printLit<Solver>(var);
        Debug("proof:sat") << std::endl;
      }
      return false;
    }
    clause1.erase(~var);
    clause2.erase(var);
    typename std::set<typename Solver::TLit>::iterator it = clause2.begin();
    for (; it != clause2.end(); ++it) {
      clause1.insert(*it);
    }
  }
  return true;
}

/// ResChain
template <class Solver>
ResChain<Solver>::ResChain(ClauseId start)
    : d_start(start), d_steps(), d_redundantLits(NULL) {}

template <class Solver>
ResChain<Solver>::~ResChain() {
  if (d_redundantLits != NULL) {
    delete d_redundantLits;
  }
}

template <class Solver>
void ResChain<Solver>::addStep(typename Solver::TLit lit, ClauseId id,
                               bool sign) {
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

/// SatProof
template <class Solver>
TSatProof<Solver>::TSatProof(Solver* solver, context::Context* context,
                             const std::string& name, bool checkRes)
    : d_name(name),
      d_emptyClauseId(ClauseIdEmpty),
      d_seenLearnt(),
      d_assumptionConflictsDebug(),
      d_solver(solver),
      d_context(context),
      d_idClause(),
      d_clauseId(),
      d_idUnit(context),
      d_unitId(context),
      d_deleted(),
      d_inputClauses(),
      d_lemmaClauses(),
      d_assumptions(),
      d_assumptionConflicts(),
      d_resolutionChains(d_context),
      d_resStack(),
      d_checkRes(checkRes),
      d_nullId(-2),
      d_temp_clauseId(),
      d_temp_idClause(),
      d_unitConflictId(context),
      d_trueLit(ClauseIdUndef),
      d_falseLit(ClauseIdUndef),
      d_seenInputs(),
      d_seenLemmas(),
      d_satProofConstructed(false),
      d_statistics(name) {
}

template <class Solver>
TSatProof<Solver>::~TSatProof() {
  // FIXME: double free if deleted clause also appears in d_seenLemmas?
  IdToSatClause::const_iterator it = d_deletedTheoryLemmas.begin();
  IdToSatClause::const_iterator end = d_deletedTheoryLemmas.end();

  for (; it != end; ++it) {
    ClauseId id = it->first;
    // otherwise deleted in next loop
    if (d_seenLemmas.find(id) == d_seenLemmas.end()) {
      delete it->second;
    }
  }

  IdToSatClause::const_iterator seen_lemma_it = d_seenLemmas.begin();
  IdToSatClause::const_iterator seen_lemma_end = d_seenLemmas.end();

  for (; seen_lemma_it != seen_lemma_end; ++seen_lemma_it) {
    delete seen_lemma_it->second;
  }

  IdToSatClause::const_iterator seen_input_it = d_seenInputs.begin();
  IdToSatClause::const_iterator seen_input_end = d_seenInputs.end();

  for (; seen_input_it != seen_input_end; ++seen_input_it) {
    delete seen_input_it->second;
  }

  typedef typename IdResMap::const_iterator ResolutionChainIterator;
  ResolutionChainIterator resolution_it = d_resolutionChains.begin();
  ResolutionChainIterator resolution_it_end = d_resolutionChains.end();
  for (; resolution_it != resolution_it_end; ++resolution_it) {
    ResChain<Solver>* current = (*resolution_it).second;
    delete current;
  }

  // It could be the case that d_resStack is not empty at destruction time
  // (for example in the SAT case).
  typename ResStack::const_iterator resolution_stack_it = d_resStack.begin();
  typename ResStack::const_iterator resolution_stack_it_end = d_resStack.end();
  for (; resolution_stack_it != resolution_stack_it_end;
       ++resolution_stack_it) {
    ResChain<Solver>* current = *resolution_stack_it;
    delete current;
  }
}

/**
 * Returns true if the resolution chain corresponding to id
 * does resolve to the clause associated to id
 * @param id
 *
 * @return
 */
template <class Solver>
bool TSatProof<Solver>::checkResolution(ClauseId id) {
  if (d_checkRes) {
    bool validRes = true;
    Assert(hasResolutionChain(id));
    const ResolutionChain& res = getResolutionChain(id);
    LitSet clause1;
    createLitSet(res.getStart(), clause1);
    const typename ResolutionChain::ResSteps& steps = res.getSteps();
    for (unsigned i = 0; i < steps.size(); i++) {
      typename Solver::TLit var = steps[i].lit;
      LitSet clause2;
      createLitSet(steps[i].id, clause2);
      if (!resolve<Solver>(var, clause1, clause2, steps[i].sign))
      {
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
        if (Debug.isOn("proof:sat")) {
          Debug("proof:sat")
              << "proof:checkResolution::literal not in computed result ";
          printLit<Solver>(c[i]);
          Debug("proof:sat") << "\n";
        }
        validRes = false;
      }
    }
    validRes = clause1.empty();
    if (!validRes) {
      if (Debug.isOn("proof:sat")) {
        Debug("proof:sat") << "proof:checkResolution::Invalid Resolution, "
                              "unremoved literals: \n";
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
bool TSatProof<Solver>::hasClauseIdForCRef(typename Solver::TCRef ref) const {
  return d_clauseId.find(ref) != d_clauseId.end();
}

template <class Solver>
ClauseId TSatProof<Solver>::getClauseIdForCRef(
    typename Solver::TCRef ref) const {
  if (d_clauseId.find(ref) == d_clauseId.end()) {
    Debug("proof:sat") << "Missing clause \n";
  }
  Assert(hasClauseIdForCRef(ref));
  return d_clauseId.find(ref)->second;
}

template <class Solver>
bool TSatProof<Solver>::hasClauseIdForLiteral(typename Solver::TLit lit) const {
  return d_unitId.find(toInt(lit)) != d_unitId.end();
}

template <class Solver>
ClauseId TSatProof<Solver>::getClauseIdForLiteral(
    typename Solver::TLit lit) const {
  Assert(hasClauseIdForLiteral(lit));
  return (*d_unitId.find(toInt(lit))).second;
}

template <class Solver>
bool TSatProof<Solver>::hasClauseRef(ClauseId id) const {
  return d_idClause.find(id) != d_idClause.end();
}

template <class Solver>
typename Solver::TCRef TSatProof<Solver>::getClauseRef(ClauseId id) const {
  if (!hasClauseRef(id)) {
    Debug("proof:sat") << "proof:getClauseRef cannot find clause " << id << " "
                       << ((d_deleted.find(id) != d_deleted.end()) ? "deleted"
                                                                   : "")
                       << (isUnit(id) ? "Unit" : "") << std::endl;
  }
  Assert(hasClauseRef(id));
  return d_idClause.find(id)->second;
}

template <class Solver>
const typename Solver::TClause& TSatProof<Solver>::getClause(
    typename Solver::TCRef ref) const {
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
  const typename Solver::TClause& cl = getClause(cref);
  for (int i = 0; i < cl.size(); ++i) {
    vec.push_back(cl[i]);
  }
}

template <class Solver>
bool TSatProof<Solver>::isUnit(ClauseId id) const {
  return d_idUnit.find(id) != d_idUnit.end();
}

template <class Solver>
typename Solver::TLit TSatProof<Solver>::getUnit(ClauseId id) const {
  Assert(isUnit(id));
  return (*d_idUnit.find(id)).second;
}

template <class Solver>
bool TSatProof<Solver>::isUnit(typename Solver::TLit lit) const {
  return d_unitId.find(toInt(lit)) != d_unitId.end();
}

template <class Solver>
ClauseId TSatProof<Solver>::getUnitId(typename Solver::TLit lit) const {
  Assert(isUnit(lit));
  return (*d_unitId.find(toInt(lit))).second;
}

template <class Solver>
bool TSatProof<Solver>::hasResolutionChain(ClauseId id) const {
  return d_resolutionChains.find(id) != d_resolutionChains.end();
}

template <class Solver>
const typename TSatProof<Solver>::ResolutionChain&
TSatProof<Solver>::getResolutionChain(ClauseId id) const {
  Assert(hasResolutionChain(id));
  const ResolutionChain* chain = (*d_resolutionChains.find(id)).second;
  return *chain;
}

template <class Solver>
bool TSatProof<Solver>::isInputClause(ClauseId id) const {
  return d_inputClauses.find(id) != d_inputClauses.end();
}

template <class Solver>
bool TSatProof<Solver>::isLemmaClause(ClauseId id) const {
  return d_lemmaClauses.find(id) != d_lemmaClauses.end();
}

template <class Solver>
bool TSatProof<Solver>::isAssumptionConflict(ClauseId id) const {
  return d_assumptionConflicts.find(id) != d_assumptionConflicts.end();
}

template <class Solver>
void TSatProof<Solver>::print(ClauseId id) const {
  if (d_deleted.find(id) != d_deleted.end()) {
    Debug("proof:sat") << "del" << id;
  } else if (isUnit(id)) {
    printLit<Solver>(getUnit(id));
  } else if (id == d_emptyClauseId) {
    Debug("proof:sat") << "empty " << std::endl;
  } else {
    typename Solver::TCRef ref = getClauseRef(id);
    printClause<Solver>(getClause(ref));
  }
}

template <class Solver>
void TSatProof<Solver>::printRes(ClauseId id) const {
  Assert(hasResolutionChain(id));
  Debug("proof:sat") << "id " << id << ": ";
  printRes(getResolutionChain(id));
}

template <class Solver>
void TSatProof<Solver>::printRes(const ResolutionChain& res) const {
  ClauseId start_id = res.getStart();

  if (Debug.isOn("proof:sat")) {
    Debug("proof:sat") << "(";
    print(start_id);
  }

  const typename ResolutionChain::ResSteps& steps = res.getSteps();
  for (unsigned i = 0; i < steps.size(); i++) {
    typename Solver::TLit v = steps[i].lit;
    ClauseId id = steps[i].id;

    if (Debug.isOn("proof:sat")) {
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
      d_inputClauses.insert(newId);
    }
    if (kind == THEORY_LEMMA) {
      Assert(d_lemmaClauses.find(newId) == d_lemmaClauses.end());
      d_lemmaClauses.insert(newId);
      Debug("pf::sat") << "TSatProof::registerClause registering a new lemma clause: "
                       << newId << " = " << *buildClause(newId)
                       << std::endl;
    }
  }

  ClauseId id = d_clauseId[clause];
  Assert(kind != INPUT || d_inputClauses.count(id));
  Assert(kind != THEORY_LEMMA || d_lemmaClauses.count(id));

  Debug("proof:sat:detailed") << "registerClause CRef: " << clause
                              << " id: " << d_clauseId[clause]
                              << "                kind: " << kind << "\n";
  // ProofManager::currentPM()->setRegisteredClauseId( d_clauseId[clause] );
  return id;
}

template <class Solver>
ClauseId TSatProof<Solver>::registerUnitClause(typename Solver::TLit lit,
                                               ClauseKind kind) {
  Debug("cores") << "registerUnitClause " << kind << std::endl;
  typename UnitIdMap::iterator it = d_unitId.find(toInt(lit));
  if (it == d_unitId.end()) {
    ClauseId newId = ProofManager::currentPM()->nextId();

    if (d_unitId.find(toInt(lit)) == d_unitId.end())
      d_unitId[toInt(lit)] = newId;
    if (d_idUnit.find(newId) == d_idUnit.end())
      d_idUnit[newId] = lit;

    if (kind == INPUT) {
      Assert(d_inputClauses.find(newId) == d_inputClauses.end());
      Debug("pf::sat") << "TSatProof::registerUnitClause: registering a new "
                          "input (UNIT CLAUSE): "
                       << lit << std::endl;
      d_inputClauses.insert(newId);
    }
    if (kind == THEORY_LEMMA) {
      Assert(d_lemmaClauses.find(newId) == d_lemmaClauses.end());
      Debug("pf::sat") << "TSatProof::registerUnitClause: registering a new lemma (UNIT CLAUSE): "
                       << lit
                       << std::endl;
      d_lemmaClauses.insert(newId);
    }
  }
  ClauseId id = d_unitId[toInt(lit)];
  Assert(kind != INPUT || d_inputClauses.count(id));
  Assert(kind != THEORY_LEMMA || d_lemmaClauses.count(id));
  Debug("proof:sat:detailed") << "registerUnitClause id: " << id
                              << " kind: " << kind << "\n";
  // ProofManager::currentPM()->setRegisteredClauseId( d_unitId[toInt(lit)] );
  return id;
}
template <class Solver>
void TSatProof<Solver>::registerTrueLit(const typename Solver::TLit lit) {
  Assert(d_trueLit == ClauseIdUndef);
  d_trueLit = registerUnitClause(lit, INPUT);
}

template <class Solver>
void TSatProof<Solver>::registerFalseLit(const typename Solver::TLit lit) {
  Assert(d_falseLit == ClauseIdUndef);
  d_falseLit = registerUnitClause(lit, INPUT);
}

template <class Solver>
ClauseId TSatProof<Solver>::getTrueUnit() const {
  Assert(d_trueLit != ClauseIdUndef);
  return d_trueLit;
}

template <class Solver>
ClauseId TSatProof<Solver>::getFalseUnit() const {
  Assert(d_falseLit != ClauseIdUndef);
  return d_falseLit;
}

template <class Solver>
void TSatProof<Solver>::registerAssumption(const typename Solver::TVar var) {
  Assert(d_assumptions.find(var) == d_assumptions.end());
  d_assumptions.insert(var);
}

template <class Solver>
ClauseId TSatProof<Solver>::registerAssumptionConflict(
    const typename Solver::TLitVec& confl) {
  Debug("proof:sat:detailed") << "registerAssumptionConflict " << std::endl;
  // Uniqueness is checked in the bit-vector proof
  // should be vars
  for (int i = 0; i < confl.size(); ++i) {
    Assert(d_assumptions.find(var(confl[i])) != d_assumptions.end());
  }
  ClauseId new_id = ProofManager::currentPM()->nextId();
  d_assumptionConflicts.insert(new_id);
  LitVector* vec_confl = new LitVector(confl.size());
  for (int i = 0; i < confl.size(); ++i) {
    vec_confl->operator[](i) = confl[i];
  }
  if (Debug.isOn("proof:sat:detailed")) {
    printClause<Solver>(*vec_confl);
    Debug("proof:sat:detailed") << "\n";
  }

  d_assumptionConflictsDebug[new_id] = vec_confl;
  return new_id;
}

template <class Solver>
void TSatProof<Solver>::removedDfs(typename Solver::TLit lit,
                                   LitSet* removedSet, LitVector& removeStack,
                                   LitSet& inClause, LitSet& seen) {
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
  for (int i = 1; i < size; i++) {
    typename Solver::TLit v = getClause(reason_ref)[i];
    if (inClause.count(v) == 0 && seen.count(v) == 0) {
      removedDfs(v, removedSet, removeStack, inClause, seen);
    }
  }
  if (seen.count(lit) == 0) {
    seen.insert(lit);
    removeStack.push_back(lit);
  }
}

template <class Solver>
void TSatProof<Solver>::removeRedundantFromRes(ResChain<Solver>* res,
                                               ClauseId id) {
  LitSet* removed = res->getRedundant();
  if (removed == NULL) {
    return;
  }

  LitSet inClause;
  createLitSet(id, inClause);

  LitVector removeStack;
  LitSet seen;
  for (typename LitSet::iterator it = removed->begin(); it != removed->end();
       ++it) {
    removedDfs(*it, removed, removeStack, inClause, seen);
  }

  for (int i = removeStack.size() - 1; i >= 0; --i) {
    typename Solver::TLit lit = removeStack[i];
    typename Solver::TCRef reason_ref = d_solver->reason(var(lit));
    ClauseId reason_id;

    if (reason_ref == Solver::TCRef_Undef) {
      Assert(isUnit(~lit));
      reason_id = getUnitId(~lit);
    } else {
      reason_id = registerClause(reason_ref, LEARNT);
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

  // Because the SAT solver can add the same clause multiple times, it
  // could be the case that a resolution chain for this clause already
  // exists (e.g. when removing units in addClause).
  if (hasResolutionChain(id)) {
    ResChain<Solver>* current = (*d_resolutionChains.find(id)).second;
    delete current;
  }

  d_resolutionChains.insert(id, res);

  if (Debug.isOn("proof:sat")) {
    printRes(id);
  }
  if (d_checkRes) {
    Assert(checkResolution(id));
  }

}

/// recording resolutions
template <class Solver>
void TSatProof<Solver>::startResChain(typename Solver::TCRef start) {
  ClauseId id = getClauseIdForCRef(start);
  ResolutionChain* res = new ResolutionChain(id);
  d_resStack.push_back(res);
}

template <class Solver>
void TSatProof<Solver>::startResChain(typename Solver::TLit start) {
  ClauseId id = getUnitId(start);
  ResolutionChain* res = new ResolutionChain(id);
  d_resStack.push_back(res);
}

template <class Solver>
void TSatProof<Solver>::addResolutionStep(typename Solver::TLit lit,
                                          typename Solver::TCRef clause,
                                          bool sign) {
  ClauseId id = registerClause(clause, LEARNT);
  ResChain<Solver>* res = d_resStack.back();
  res->addStep(lit, id, sign);
}

template <class Solver>
void TSatProof<Solver>::endResChain(ClauseId id) {
  Debug("proof:sat:detailed") << "endResChain " << id << "\n";
  Assert(d_resStack.size() > 0);
  ResChain<Solver>* res = d_resStack.back();
  registerResolution(id, res);
  d_resStack.pop_back();
}

template <class Solver>
void TSatProof<Solver>::endResChain(typename Solver::TLit lit) {
  Assert(d_resStack.size() > 0);
  ClauseId id = registerUnitClause(lit, LEARNT);
  Debug("proof:sat:detailed") << "endResChain unit " << id << "\n";
  ResolutionChain* res = d_resStack.back();
  d_glueMap[id] = 1;
  registerResolution(id, res);
  d_resStack.pop_back();
}

template <class Solver>
void TSatProof<Solver>::cancelResChain() {
  Assert(d_resStack.size() > 0);
  ResolutionChain* back = d_resStack.back();
  delete back;
  d_resStack.pop_back();
}

template <class Solver>
void TSatProof<Solver>::storeLitRedundant(typename Solver::TLit lit) {
  Assert(d_resStack.size() > 0);
  ResolutionChain* res = d_resStack.back();
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

  if (isUnit(lit)) {
    ClauseId id = getClauseIdForLiteral(lit);
    Assert(hasResolutionChain(id) || isInputClause(id) || isLemmaClause(id));
    return id;
  }
  typename Solver::TCRef reason_ref = d_solver->reason(var(lit));
  Assert(reason_ref != Solver::TCRef_Undef);

  ClauseId reason_id = registerClause(reason_ref, LEARNT);

  ResChain<Solver>* res = new ResChain<Solver>(reason_id);
  // Here, the call to resolveUnit() can reallocate memory in the
  // clause allocator.  So reload reason ptr each time.
  const typename Solver::TClause& initial_reason = getClause(reason_ref);
  size_t current_reason_size = initial_reason.size();
  for (size_t i = 0; i < current_reason_size; i++) {
    const typename Solver::TClause& current_reason = getClause(reason_ref);
    current_reason_size = current_reason.size();
    typename Solver::TLit l = current_reason[i];
    if (lit != l) {
      ClauseId res_id = resolveUnit(~l);
      res->addStep(l, res_id, !sign(l));
    }
  }
  ClauseId unit_id = registerUnitClause(lit, LEARNT);
  registerResolution(unit_id, res);
  return unit_id;
}

template <class Solver>
ClauseId TSatProof<Solver>::storeUnitConflict(
    typename Solver::TLit conflict_lit, ClauseKind kind) {
  Debug("cores") << "STORE UNIT CONFLICT" << std::endl;
  Assert(!d_unitConflictId.isSet());
  d_unitConflictId.set(registerUnitClause(conflict_lit, kind));
  Debug("proof:sat:detailed") << "storeUnitConflict " << d_unitConflictId.get()
                              << "\n";
  return d_unitConflictId.get();
}

template <class Solver>
void TSatProof<Solver>::finalizeProof(typename Solver::TCRef conflict_ref) {
  Assert(d_resStack.size() == 0);
  Assert(conflict_ref != Solver::TCRef_Undef);
  ClauseId conflict_id;
  if (conflict_ref == Solver::TCRef_Lazy) {
    Assert(d_unitConflictId.isSet());
    conflict_id = d_unitConflictId.get();

    ResChain<Solver>* res = new ResChain<Solver>(conflict_id);
    typename Solver::TLit lit = d_idUnit[conflict_id];
    ClauseId res_id = resolveUnit(~lit);
    res->addStep(lit, res_id, !sign(lit));
    registerResolution(d_emptyClauseId, res);
    return;

  } else {
    Assert(!d_unitConflictId.isSet());
    conflict_id = registerClause(conflict_ref, LEARNT);  // FIXME
  }

  if (Debug.isOn("proof:sat")) {
    Debug("proof:sat") << "proof::finalizeProof Final Conflict ";
    print(conflict_id);
    Debug("proof:sat") << std::endl;
  }

  ResChain<Solver>* res = new ResChain<Solver>(conflict_id);
  // Here, the call to resolveUnit() can reallocate memory in the
  // clause allocator.  So reload conflict ptr each time.
  for (int i = 0; i < getClause(conflict_ref).size(); ++i) {
    const typename Solver::TClause& conflict = getClause(conflict_ref);
    typename Solver::TLit lit = conflict[i];
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
  ClauseId id = getClauseIdForCRef(oldref);
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
  if (hasClauseIdForCRef(clause)) {
    ClauseId id = getClauseIdForCRef(clause);
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

template <class Solver>
void TSatProof<Solver>::constructProof(ClauseId conflict) {
  d_satProofConstructed = true;
  collectClauses(conflict);
}

template <class Solver>
void TSatProof<Solver>::refreshProof(ClauseId conflict) {
  IdToSatClause::const_iterator seen_lemma_it = d_seenLemmas.begin();
  IdToSatClause::const_iterator seen_lemma_end = d_seenLemmas.end();

  for (; seen_lemma_it != seen_lemma_end; ++seen_lemma_it) {
    if (d_deletedTheoryLemmas.find(seen_lemma_it->first) == d_deletedTheoryLemmas.end())
      delete seen_lemma_it->second;
  }

  IdToSatClause::const_iterator seen_input_it = d_seenInputs.begin();
  IdToSatClause::const_iterator seen_input_end = d_seenInputs.end();

  for (; seen_input_it != seen_input_end; ++seen_input_it) {
    delete seen_input_it->second;
  }

  d_seenInputs.clear();
  d_seenLemmas.clear();
  d_seenLearnt.clear();

  collectClauses(conflict);
}

template <class Solver>
bool TSatProof<Solver>::proofConstructed() const {
  return d_satProofConstructed;
}

template <class Solver>
prop::SatClause* TSatProof<Solver>::buildClause(ClauseId id) {
  if (isUnit(id)) {
    typename Solver::TLit lit = getUnit(id);
    prop::SatLiteral sat_lit = toSatLiteral<Solver>(lit);
    prop::SatClause* clause = new prop::SatClause();
    clause->push_back(sat_lit);
    return clause;
  }

  if (isDeleted(id)) {
    prop::SatClause* clause = d_deletedTheoryLemmas.find(id)->second;
    return clause;
  }

  typename Solver::TCRef ref = getClauseRef(id);
  const typename Solver::TClause& minisat_cl = getClause(ref);
  prop::SatClause* clause = new prop::SatClause();
  toSatClause<Solver>(minisat_cl, *clause);
  return clause;
}

template <class Solver>
bool TSatProof<Solver>::derivedEmptyClause() const {
  return hasResolutionChain(d_emptyClauseId);
}

template <class Solver>
void TSatProof<Solver>::collectClauses(ClauseId id) {
  if (d_seenInputs.find(id) != d_seenInputs.end() ||
      d_seenLemmas.find(id) != d_seenLemmas.end() ||
      d_seenLearnt.find(id) != d_seenLearnt.end()) {
    return;
  }

  if (isInputClause(id)) {
    d_seenInputs.insert(std::make_pair(id, buildClause(id)));
    return;
  } else if (isLemmaClause(id)) {
    d_seenLemmas.insert(std::make_pair(id, buildClause(id)));
    return;
  } else if (!isAssumptionConflict(id)) {
    d_seenLearnt.insert(id);
  }

  const ResolutionChain& res = getResolutionChain(id);
  const typename ResolutionChain::ResSteps& steps = res.getSteps();
  ClauseId start = res.getStart();
  collectClauses(start);

  for (size_t i = 0; i < steps.size(); i++) {
    collectClauses(steps[i].id);
  }
}

template <class Solver>
void TSatProof<Solver>::collectClausesUsed(IdToSatClause& inputs,
                                           IdToSatClause& lemmas) {
  inputs = d_seenInputs;
  lemmas = d_seenLemmas;
}

template <class Solver>
void TSatProof<Solver>::storeClauseGlue(ClauseId clause, int glue) {
  Assert(d_glueMap.find(clause) == d_glueMap.end());
  d_glueMap.insert(std::make_pair(clause, glue));
}

template <class Solver>
TSatProof<Solver>::Statistics::Statistics(const std::string& prefix)
    : d_numLearnedClauses("satproof::" + prefix + "::NumLearnedClauses", 0),
      d_numLearnedInProof("satproof::" + prefix + "::NumLearnedInProof", 0),
      d_numLemmasInProof("satproof::" + prefix + "::NumLemmasInProof", 0),
      d_avgChainLength("satproof::" + prefix + "::AvgResChainLength"),
      d_resChainLengths("satproof::" + prefix + "::ResChainLengthsHist"),
      d_usedResChainLengths("satproof::" + prefix +
                            "::UsedResChainLengthsHist"),
      d_clauseGlue("satproof::" + prefix + "::ClauseGlueHist"),
      d_usedClauseGlue("satproof::" + prefix + "::UsedClauseGlueHist") {
  smtStatisticsRegistry()->registerStat(&d_numLearnedClauses);
  smtStatisticsRegistry()->registerStat(&d_numLearnedInProof);
  smtStatisticsRegistry()->registerStat(&d_numLemmasInProof);
  smtStatisticsRegistry()->registerStat(&d_avgChainLength);
  smtStatisticsRegistry()->registerStat(&d_resChainLengths);
  smtStatisticsRegistry()->registerStat(&d_usedResChainLengths);
  smtStatisticsRegistry()->registerStat(&d_clauseGlue);
  smtStatisticsRegistry()->registerStat(&d_usedClauseGlue);
}

template <class Solver>
TSatProof<Solver>::Statistics::~Statistics() {
  smtStatisticsRegistry()->unregisterStat(&d_numLearnedClauses);
  smtStatisticsRegistry()->unregisterStat(&d_numLearnedInProof);
  smtStatisticsRegistry()->unregisterStat(&d_numLemmasInProof);
  smtStatisticsRegistry()->unregisterStat(&d_avgChainLength);
  smtStatisticsRegistry()->unregisterStat(&d_resChainLengths);
  smtStatisticsRegistry()->unregisterStat(&d_usedResChainLengths);
  smtStatisticsRegistry()->unregisterStat(&d_clauseGlue);
  smtStatisticsRegistry()->unregisterStat(&d_usedClauseGlue);
}

inline std::ostream& operator<<(std::ostream& out, CVC4::ClauseKind k) {
  switch (k) {
    case CVC4::INPUT:
      out << "INPUT";
      break;
    case CVC4::THEORY_LEMMA:
      out << "THEORY_LEMMA";
      break;
    case CVC4::LEARNT:
      out << "LEARNT";
      break;
    default:
      out << "ClauseKind Unknown! [" << unsigned(k) << "]";
  }

  return out;
}

} /* CVC4 namespace */

#endif /* CVC4__SAT__PROOF_IMPLEMENTATION_H */
