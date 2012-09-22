/*********************                                                        */
/*! \file quantifiers_engine.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Theory instantiator, Instantiation Engine classes
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS_ENGINE_H
#define __CVC4__THEORY__QUANTIFIERS_ENGINE_H

#include "theory/theory.h"
#include "util/hash.h"
#include "theory/quantifiers/inst_match.h"
#include "theory/rewriterules/rr_inst_match.h"

#include "util/statistics_registry.h"

#include <ext/hash_set>
#include <iostream>
#include <map>

namespace CVC4 {

class TheoryEngine;

namespace theory {

class QuantifiersEngine;

class InstStrategy {
public:
  enum Status {
    STATUS_UNFINISHED,
    STATUS_UNKNOWN,
    STATUS_SAT,
  };/* enum Status */
protected:
  /** reference to the instantiation engine */
  QuantifiersEngine* d_quantEngine;
protected:
  /** giving priorities */
  std::vector< InstStrategy* > d_priority_over;
  /** do not instantiate list */
  std::vector< Node > d_no_instantiate;
  std::vector< Node > d_no_instantiate_temp;
  /** reset instantiation */
  virtual void processResetInstantiationRound( Theory::Effort effort ) = 0;
  /** process method */
  virtual int process( Node f, Theory::Effort effort, int e ) = 0;
public:
  InstStrategy( QuantifiersEngine* ie ) : d_quantEngine( ie ){}
  virtual ~InstStrategy(){}

  /** reset instantiation */
  void resetInstantiationRound( Theory::Effort effort );
  /** do instantiation round method */
  int doInstantiation( Node f, Theory::Effort effort, int e );
  /** update status */
  static void updateStatus( int& currStatus, int addStatus ){
    if( addStatus==STATUS_UNFINISHED ){
      currStatus = STATUS_UNFINISHED;
    }else if( addStatus==STATUS_UNKNOWN ){
      if( currStatus==STATUS_SAT ){
        currStatus = STATUS_UNKNOWN;
      }
    }
  }
  /** identify */
  virtual std::string identify() const { return std::string("Unknown"); }
public:
  /** set priority */
  void setPriorityOver( InstStrategy* is ) { d_priority_over.push_back( is ); }
  /** set no instantiate */
  void setNoInstantiate( Node n ) { d_no_instantiate.push_back( n ); }
  /** should instantiate */
  bool shouldInstantiate( Node n ) {
    return std::find( d_no_instantiate_temp.begin(), d_no_instantiate_temp.end(), n )==d_no_instantiate_temp.end();
  }
};/* class InstStrategy */

class QuantifiersModule {
protected:
  QuantifiersEngine* d_quantEngine;
public:
  QuantifiersModule( QuantifiersEngine* qe ) : d_quantEngine( qe ){}
  ~QuantifiersModule(){}
  //get quantifiers engine
  QuantifiersEngine* getQuantifiersEngine() { return d_quantEngine; }
  /* Call during check registerQuantifier has already been called */
  virtual void check( Theory::Effort e ) = 0;
  /* Called for new quantifiers */
  virtual void registerQuantifier( Node n ) = 0;
  virtual void assertNode( Node n ) = 0;
  virtual void propagate( Theory::Effort level ){}
  virtual Node getNextDecisionRequest() { return TNode::null(); }
  virtual Node explain(TNode n) = 0;
};/* class QuantifiersModule */

namespace quantifiers {
  class InstantiationEngine;
  class ModelEngine;
  class TermDb;
  class FirstOrderModel;
}/* CVC4::theory::quantifiers */


class QuantifiersEngine {
  friend class quantifiers::InstantiationEngine;
  friend class quantifiers::ModelEngine;
  friend class inst::InstMatch;
private:
  typedef context::CDHashMap< Node, bool, NodeHashFunction > BoolMap;
  /** reference to theory engine object */
  TheoryEngine* d_te;
  /** vector of modules for quantifiers */
  std::vector< QuantifiersModule* > d_modules;
  /** instantiation engine */
  quantifiers::InstantiationEngine* d_inst_engine;
  /** model engine */
  quantifiers::ModelEngine* d_model_engine;
  /** equality query class */
  EqualityQuery* d_eq_query;
public:
  /** list of all quantifiers (pre-rewrite) */
  std::vector< Node > d_quants;
  /** list of all quantifiers (post-rewrite) */
  std::vector< Node > d_r_quants;
  /** map from quantifiers to whether they are active */
  BoolMap d_active;
  /** lemmas produced */
  std::map< Node, bool > d_lemmas_produced;
  /** lemmas waiting */
  std::vector< Node > d_lemmas_waiting;
  /** has added lemma this round */
  bool d_hasAddedLemma;
  /** inst matches produced for each quantifier */
  std::map< Node, inst::InstMatchTrie > d_inst_match_trie;
  /** owner of quantifiers */
  std::map< Node, Theory* > d_owner;
  /** term database */
  quantifiers::TermDb* d_term_db;
  /** extended model object */
  quantifiers::FirstOrderModel* d_model;
  /** has the model been set? */
  bool d_model_set;
  /** has resetInstantiationRound() been called on this check(...) */
  bool d_resetInstRound;
  /** universal quantifiers that have been rewritten */
  std::map< Node, std::vector< Node > > d_quant_rewritten;
  /** map from rewritten universal quantifiers to the quantifier they are the consequence of */
  std::map< Node, Node > d_rewritten_quant;
private:
  /** for computing relavance */
  /** map from quantifiers to symbols they contain */
  std::map< Node, std::vector< Node > > d_syms;
  /** map from symbols to quantifiers */
  std::map< Node, std::vector< Node > > d_syms_quants;
  /** relevance for quantifiers and symbols */
  std::map< Node, int > d_relevance;
  /** compute symbols */
  void computeSymbols( Node n, std::vector< Node >& syms );
private:
  /** helper functions compute phase requirements */
  static void computePhaseReqs2( Node n, bool polarity, std::map< Node, int >& phaseReqs );

  KEEP_STATISTIC(TimerStat, d_time, "theory::QuantifiersEngine::time");

public:
  QuantifiersEngine(context::Context* c, TheoryEngine* te);
  ~QuantifiersEngine();
  /** get instantiator for id */
  Instantiator* getInstantiator( theory::TheoryId id );
  /** get theory engine */
  TheoryEngine* getTheoryEngine() { return d_te; }
  /** get equality query object for the given type. The default is the
      generic one */
  inst::EqualityQuery* getEqualityQuery(TypeNode t);
  inst::EqualityQuery* getEqualityQuery() {
    return d_eq_query;
  }
  /** get equality query object for the given type. The default is the
      one of UF */
  rrinst::CandidateGenerator* getRRCanGenClasses(TypeNode t);
  rrinst::CandidateGenerator* getRRCanGenClass(TypeNode t);
  /* generic candidate generator */
  rrinst::CandidateGenerator* getRRCanGenClasses();
  rrinst::CandidateGenerator* getRRCanGenClass();
  /** get instantiation engine */
  quantifiers::InstantiationEngine* getInstantiationEngine() { return d_inst_engine; }
  /** get model engine */
  quantifiers::ModelEngine* getModelEngine() { return d_model_engine; }
  /** get default sat context for quantifiers engine */
  context::Context* getSatContext();
  /** get default output channel for the quantifiers engine */
  OutputChannel& getOutputChannel();
  /** get default valuation for the quantifiers engine */
  Valuation& getValuation();
public:
  /** check at level */
  void check( Theory::Effort e );
  /** register (non-rewritten) quantifier */
  void registerQuantifier( Node f );
  /** register (non-rewritten) quantifier */
  void registerPattern( std::vector<Node> & pattern);
  /** assert (universal) quantifier */
  void assertNode( Node f );
  /** propagate */
  void propagate( Theory::Effort level );
  /** get next decision request */
  Node getNextDecisionRequest();
  /** reset instantiation round */
  void resetInstantiationRound( Theory::Effort level );

  //create inst variable
  std::vector<Node> createInstVariable( std::vector<Node> & vars );
public:
  /** add lemma lem */
  bool addLemma( Node lem );
  /** instantiate f with arguments terms */
  bool addInstantiation( Node f, std::vector< Node >& vars, std::vector< Node >& terms );
  /** do instantiation specified by m */
  bool addInstantiation( Node f, InstMatch& m, bool makeComplete = true );
  /** split on node n */
  bool addSplit( Node n, bool reqPhase = false, bool reqPhasePol = true );
  /** add split equality */
  bool addSplitEquality( Node n1, Node n2, bool reqPhase = false, bool reqPhasePol = true );
  /** has added lemma */
  bool hasAddedLemma() { return !d_lemmas_waiting.empty() || d_hasAddedLemma; }
  /** flush lemmas */
  void flushLemmas( OutputChannel* out );
  /** get number of waiting lemmas */
  int getNumLemmasWaiting() { return (int)d_lemmas_waiting.size(); }
public:
  /** get number of quantifiers */
  int getNumQuantifiers() { return (int)d_quants.size(); }
  /** get quantifier */
  Node getQuantifier( int i ) { return d_quants[i]; }
  /** set active */
  void setActive( Node n, bool val ) { d_active[n] = val; }
  /** get active */
  bool getActive( Node n ) { return d_active.find( n )!=d_active.end() && d_active[n]; }
public:
  /** phase requirements for each quantifier for each instantiation literal */
  std::map< Node, std::map< Node, bool > > d_phase_reqs;
  std::map< Node, std::map< Node, bool > > d_phase_reqs_equality;
  std::map< Node, std::map< Node, Node > > d_phase_reqs_equality_term;
public:
  /** is phase required */
  bool isPhaseReq( Node f, Node lit ) { return d_phase_reqs[f].find( lit )!=d_phase_reqs[f].end(); }
  /** get phase requirement */
  bool getPhaseReq( Node f, Node lit ) { return d_phase_reqs[f].find( lit )==d_phase_reqs[f].end() ? false : d_phase_reqs[f][ lit ]; }
  /** get term req terms */
  void getPhaseReqTerms( Node f, std::vector< Node >& nodes );
  /** helper functions compute phase requirements */
  static void computePhaseReqs( Node n, bool polarity, std::map< Node, bool >& phaseReqs );
  /** compute phase requirements */
  void generatePhaseReqs( Node f, Node n );
public:
  /** has owner */
  bool hasOwner( Node f ) { return d_owner.find( f )!=d_owner.end(); }
  /** get owner */
  Theory* getOwner( Node f ) { return d_owner[f]; }
  /** set owner */
  void setOwner( Node f, Theory* t ) { d_owner[f] = t; }
public:
  /** get model */
  quantifiers::FirstOrderModel* getModel() { return d_model; }
  /** get term database */
  quantifiers::TermDb* getTermDatabase() { return d_term_db; }
  /** add term to database */
  void addTermToDatabase( Node n, bool withinQuant = false );
private:
  /** set relevance */
  void setRelevance( Node s, int r );
public:
  /** get relevance */
  int getRelevance( Node s ) { return d_relevance.find( s )==d_relevance.end() ? -1 : d_relevance[s]; }
  /** get number of quantifiers for symbol s */
  int getNumQuantifiersForSymbol( Node s ) { return (int)d_syms_quants[s].size(); }
public:
  /** statistics class */
  class Statistics {
  public:
    IntStat d_num_quant;
    IntStat d_instantiation_rounds;
    IntStat d_instantiation_rounds_lc;
    IntStat d_instantiations;
    IntStat d_max_instantiation_level;
    IntStat d_splits;
    IntStat d_total_inst_var;
    IntStat d_total_inst_var_unspec;
    IntStat d_inst_unspec;
    IntStat d_inst_duplicate;
    IntStat d_lit_phase_req;
    IntStat d_lit_phase_nreq;
    IntStat d_triggers;
    IntStat d_simple_triggers;
    IntStat d_multi_triggers;
    IntStat d_multi_trigger_instantiations;
    IntStat d_term_in_termdb;
    IntStat d_num_mono_candidates;
    IntStat d_num_mono_candidates_new_term;
    IntStat d_num_multi_candidates;
    IntStat d_mono_candidates_cache_hit;
    IntStat d_mono_candidates_cache_miss;
    IntStat d_multi_candidates_cache_hit;
    IntStat d_multi_candidates_cache_miss;
    Statistics();
    ~Statistics();
  };/* class QuantifiersEngine::Statistics */
  Statistics d_statistics;
public:
  /** options */
  bool d_optInstCheckDuplicate;
  bool d_optInstMakeRepresentative;
  bool d_optInstAddSplits;
  bool d_optMatchIgnoreModelBasis;
  bool d_optInstLimitActive;
  int d_optInstLimit;
};/* class QuantifiersEngine */



/** equality query object using theory engine */
class EqualityQueryQuantifiersEngine : public EqualityQuery
{
private:
  /** pointer to theory engine */
  QuantifiersEngine* d_qe;
public:
  EqualityQueryQuantifiersEngine( QuantifiersEngine* qe ) : d_qe( qe ){}
  ~EqualityQueryQuantifiersEngine(){}
  /** general queries about equality */
  bool hasTerm( Node a );
  Node getRepresentative( Node a );
  bool areEqual( Node a, Node b );
  bool areDisequal( Node a, Node b );
  Node getInternalRepresentative( Node a );
  eq::EqualityEngine* getEngine();
  void getEquivalenceClass( Node a, std::vector< Node >& eqc );
}; /* EqualityQueryQuantifiersEngine */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS_ENGINE_H */
