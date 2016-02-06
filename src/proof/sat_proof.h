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

#ifndef __CVC4__SAT__PROOF_H
#define __CVC4__SAT__PROOF_H

#include <stdint.h>
#include <ext/hash_map>
#include <ext/hash_set>
#include <iosfwd>
#include <set>
#include <sstream>
#include <vector>
#include "expr/expr.h"
#include "proof/proof_manager.h"
#include "util/proof.h"
#include "util/statistics_registry.h"


namespace CVC4 {


class CnfProof;

/**
 * Helper debugging functions
 */
template <class Solver> void printDebug(typename Solver::TLit l);
template <class Solver> void printDebug(typename Solver::TClause& c);

enum ClauseKind {
  INPUT,
  THEORY_LEMMA, // we need to distinguish because we must reprove deleted theory lemmas
  LEARNT
};/* enum ClauseKind */


template <class Solver>
struct ResStep {
  typename Solver::TLit lit;
  ClauseId id;
  bool sign;
  ResStep(typename Solver::TLit l, ClauseId i, bool s) :
    lit(l),
    id(i),
    sign(s)
  {}
};/* struct ResStep */

template <class Solver>
class ResChain {
public:
  typedef std::vector< ResStep<Solver> > ResSteps;
  typedef std::set < typename Solver::TLit> LitSet;

private:
  ClauseId       d_start;
  ResSteps       d_steps;
  LitSet*        d_redundantLits;
public:
  ResChain(ClauseId start);
  void addStep(typename Solver::TLit, ClauseId, bool);
  bool redundantRemoved() { return (d_redundantLits == NULL || d_redundantLits->empty()); }
  void addRedundantLit(typename Solver::TLit lit);
  ~ResChain();
  // accessor methods
  ClauseId  getStart()     { return d_start; }
  ResSteps& getSteps()     { return d_steps; }
  LitSet*   getRedundant() { return d_redundantLits; }
};/* class ResChain */

template <class Solver> class ProofProxy;

class CnfProof;

template<class Solver>
class TSatProof {
protected:
  typedef std::set < typename Solver::TLit> LitSet;
  typedef std::set < typename Solver::TVar> VarSet;
  typedef std::hash_map < ClauseId, typename Solver::TCRef > IdCRefMap;
  typedef std::hash_map < typename Solver::TCRef, ClauseId > ClauseIdMap;
  typedef std::hash_map < ClauseId, typename Solver::TLit>   IdUnitMap;
  typedef std::hash_map < int, ClauseId>            UnitIdMap; 
  typedef std::hash_map < ClauseId, ResChain<Solver>* >      IdResMap;
  typedef std::hash_map < ClauseId, uint64_t >      IdProofRuleMap;
  typedef std::vector   < ResChain<Solver>* >       ResStack;
  //typedef std::hash_map <ClauseId, prop::SatClause* >     IdToSatClause;
  typedef std::set < ClauseId > IdSet;
  typedef std::vector < typename Solver::TLit > LitVector;
  typedef __gnu_cxx::hash_map<ClauseId, typename Solver::TClause& > IdToMinisatClause;
  typedef __gnu_cxx::hash_map<ClauseId, LitVector* > IdToConflicts;
  
  typename Solver::Solver*    d_solver;
  CnfProof* d_cnfProof; 
  
  // clauses
  IdCRefMap           d_idClause;
  ClauseIdMap         d_clauseId;
  IdUnitMap           d_idUnit;
  UnitIdMap           d_unitId;
  IdHashSet           d_deleted;
  IdToSatClause       d_deletedTheoryLemmas;

protected:
  IdHashSet           d_inputClauses;
  IdHashSet           d_lemmaClauses;
  VarSet              d_assumptions; // assumption literals for bv solver
  IdHashSet           d_assumptionConflicts; // assumption conflicts not actually added to SAT solver
  IdToConflicts       d_assumptionConflictsDebug;
  
  // resolutions
  IdResMap            d_resChains;
  ResStack            d_resStack;
  bool                d_checkRes;

  const ClauseId      d_emptyClauseId;
  const ClauseId      d_nullId;
  // proxy class to break circular dependencies
  ProofProxy<Solver>*         d_proxy;

  // temporary map for updating CRefs
  ClauseIdMap         d_temp_clauseId;
  IdCRefMap           d_temp_idClause;

  // unit conflict
  ClauseId d_unitConflictId;
  bool d_storedUnitConflict;

  ClauseId d_trueLit;
  ClauseId d_falseLit;
  
  std::string d_name;
public:
  TSatProof(Solver* solver, const std::string& name, bool checkRes = false);
  virtual ~TSatProof();
  void setCnfProof(CnfProof* cnf_proof);
protected:
  void print(ClauseId id);
  void printRes(ClauseId id);
  void printRes(ResChain<Solver>* res);

  bool isInputClause(ClauseId id);
  bool isLemmaClause(ClauseId id);
  bool isAssumptionConflict(ClauseId id);
  bool isUnit(ClauseId id);
  bool isUnit(typename Solver::TLit lit);
  bool hasResolution(ClauseId id);
  void createLitSet(ClauseId id, LitSet& set);
  void registerResolution(ClauseId id, ResChain<Solver>* res);

  ClauseId      getClauseId(typename Solver::TCRef clause);
  ClauseId      getClauseId(typename Solver::TLit lit);
  typename Solver::TCRef getClauseRef(ClauseId id);
  typename Solver::TLit  getUnit(ClauseId id);
  ClauseId      getUnitId(typename Solver::TLit lit);
  typename Solver::TClause& getClause(typename Solver::TCRef ref);
  void getLitVec(ClauseId id, LitVector& vec);
  virtual void toStream(std::ostream& out);

  bool checkResolution(ClauseId id);
  /**
   * Constructs a resolution tree that proves lit
   * and returns the ClauseId for the unit clause lit
   * @param lit the literal we are proving
   *
   * @return
   */
  ClauseId resolveUnit(typename Solver::TLit lit);
  /**
   * Does a depth first search on removed literals and adds the literals
   * to be removed in the proper order to the stack.
   *
   * @param lit the literal we are recursing on
   * @param removedSet the previously computed set of redundant literals
   * @param removeStack the stack of literals in reverse order of resolution
   */
  void removedDfs(typename Solver::TLit lit, LitSet* removedSet, LitVector& removeStack, LitSet& inClause, LitSet& seen);
  void removeRedundantFromRes(ResChain<Solver>* res, ClauseId id);
public:
  void startResChain(typename Solver::TLit start);
  void startResChain(typename Solver::TCRef start);
  void addResolutionStep(typename Solver::TLit lit, typename Solver::TCRef clause, bool sign);
  /**
   * Pops the current resolution of the stack and stores it
   * in the resolution map. Also registers the 'clause' parameter
   * @param clause the clause the resolution is proving
   */
  //void endResChain(typename Solver::TCRef clause);
  void endResChain(typename Solver::TLit lit);
  void endResChain(ClauseId id);
  /** 
   * Pops the current resolution of the stack *without* storing it. 
   * 
   */
  void cancelResChain();

  /**
   * Stores in the current derivation the redundant literals that were
   * eliminated from the conflict clause during conflict clause minimization.
   * @param lit the eliminated literal
   */
  void storeLitRedundant(typename Solver::TLit lit);

  /// update the CRef Id maps when Minisat does memory reallocation x
  void updateCRef(typename Solver::TCRef old_ref, typename Solver::TCRef new_ref);
  void finishUpdateCRef();

  /**
   * Constructs the empty clause resolution from the final conflict
   *
   * @param conflict
   */
  void finalizeProof(typename Solver::TCRef conflict);

  /// clause registration methods

  ClauseId registerClause(const typename Solver::TCRef clause,
			  ClauseKind kind);
  ClauseId registerUnitClause(const typename Solver::TLit lit,
			      ClauseKind kind);
  void registerTrueLit(const typename Solver::TLit lit);
  void registerFalseLit(const typename Solver::TLit lit);

  ClauseId getTrueUnit() const;
  ClauseId getFalseUnit() const;

  
  void registerAssumption(const typename Solver::TVar var);
  ClauseId registerAssumptionConflict(const typename Solver::TLitVec& confl);
  
  ClauseId storeUnitConflict(typename Solver::TLit lit,
                             ClauseKind kind);
 
  /**
   * Marks the deleted clauses as deleted. Note we may still use them in the final
   * resolution.
   * @param clause
   */
  void markDeleted(typename Solver::TCRef clause);
  bool isDeleted(ClauseId id) { return d_deleted.find(id) != d_deleted.end(); }
  /**
   * Constructs the resolution of ~q and resolves it with the current
   * resolution thus eliminating q from the current clause
   * @param q the literal to be resolved out
   */
  void resolveOutUnit(typename Solver::TLit q);
  /**
   * Constructs the resolution of the literal lit. Called when a clause
   * containing lit becomes satisfied and is removed.
   * @param lit
   */
  void storeUnitResolution(typename Solver::TLit lit);

  ProofProxy<Solver>* getProxy() {return d_proxy; }
  /**
   * Constructs the SAT proof for the given clause,
   * by collecting the needed clauses in the d_seen
   * data-structures, also notifying the proofmanager.
   */
  void constructProof(ClauseId id);
  void constructProof() {
    constructProof(d_emptyClauseId);
  }
  void collectClauses(ClauseId id);
  prop::SatClause* buildClause(ClauseId id);
protected:
  IdSet               d_seenLearnt;
  IdToSatClause          d_seenInputs;
  IdToSatClause          d_seenLemmas;

  std::string varName(typename Solver::TLit lit);
  std::string clauseName(ClauseId id);


  void addToProofManager(ClauseId id, ClauseKind kind);
  void addToCnfProof(ClauseId id);
public:
  virtual void printResolution(ClauseId id, std::ostream& out, std::ostream& paren) = 0;
  virtual void printResolutions(std::ostream& out, std::ostream& paren) = 0;
  virtual void printResolutionEmptyClause(std::ostream& out, std::ostream& paren) = 0;
  virtual void printAssumptionsResolution(ClauseId id, std::ostream& out, std::ostream& paren) = 0;


  void collectClausesUsed(IdToSatClause& inputs,
                          IdToSatClause& lemmas);

  void storeClauseGlue(ClauseId clause, int glue);

private:
  __gnu_cxx::hash_map<ClauseId, int> d_glueMap; 
  struct Statistics {
    IntStat d_numLearnedClauses;
    IntStat d_numLearnedInProof;
    IntStat d_numLemmasInProof;
    AverageStat d_avgChainLength;
    HistogramStat<uint64_t> d_resChainLengths;
    HistogramStat<uint64_t> d_usedResChainLengths;
    HistogramStat<uint64_t> d_clauseGlue;
    HistogramStat<uint64_t> d_usedClauseGlue;
    Statistics(const std::string& name);
    ~Statistics();
  };

  Statistics d_statistics;
};/* class TSatProof */


template <class S>
class ProofProxy {
private:
  TSatProof<S>* d_proof;
public:
  ProofProxy(TSatProof<S>* pf);
  void updateCRef(typename S::TCRef oldref, typename S::TCRef newref);
};/* class ProofProxy */


template <class SatSolver> 
class LFSCSatProof : public TSatProof<SatSolver> {
private:

public:
  LFSCSatProof(SatSolver* solver, const std::string& name, bool checkRes = false)
    : TSatProof<SatSolver>(solver, name, checkRes)
  {}
  virtual void printResolution(ClauseId id, std::ostream& out, std::ostream& paren);
  virtual void printResolutions(std::ostream& out, std::ostream& paren);
  virtual void printResolutionEmptyClause(std::ostream& out, std::ostream& paren);
  virtual void printAssumptionsResolution(ClauseId id, std::ostream& out, std::ostream& paren);
};/* class LFSCSatProof */



template<class Solver>
prop::SatLiteral toSatLiteral(typename Solver::TLit lit); 


/** 
* Convert from minisat clause to SatClause
* 
* @param minisat_cl 
* @param sat_cl 
*/
template<class Solver>
void toSatClause(const typename Solver::TClause& minisat_cl,
                 prop::SatClause& sat_cl);


}/* CVC4 namespace */

#endif /* __CVC4__SAT__PROOF_H */
