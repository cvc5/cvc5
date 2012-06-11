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
#include "theory/trigger.h"

#include "util/stats.h"

#include <ext/hash_set>
#include <iostream>
#include <map>

namespace CVC4 {

class TheoryEngine;

// attribute for "contains instantiation constants from"
struct InstConstantAttributeId {};
typedef expr::Attribute<InstConstantAttributeId, Node> InstConstantAttribute;

struct InstLevelAttributeId {};
typedef expr::Attribute<InstLevelAttributeId, uint64_t> InstLevelAttribute;

struct InstVarNumAttributeId {};
typedef expr::Attribute<InstVarNumAttributeId, uint64_t> InstVarNumAttribute;

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
  virtual int process( Node f, Theory::Effort effort, int e, int limitInst = 0 ) = 0;
public:
  InstStrategy( QuantifiersEngine* ie ) : d_quantEngine( ie ){}
  virtual ~InstStrategy(){}

  /** reset instantiation */
  void resetInstantiationRound( Theory::Effort effort );
  /** do instantiation round method */
  int doInstantiation( Node f, Theory::Effort effort, int e, int limitInst = 0 );
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
public:
  QuantifiersModule(){}
  ~QuantifiersModule(){}
  /* Call during check registerQuantifier has already been called */
  virtual void check( Theory::Effort e ) = 0;
  /* Called for new quantifiers */
  virtual void registerQuantifier( Node n ) = 0;
  virtual void assertNode( Node n ) = 0;
  virtual void propagate( Theory::Effort level ) = 0;
  virtual Node explain(TNode n) = 0;
};/* class QuantifiersModule */

class TermArgTrie {
private:
  bool addTerm2( QuantifiersEngine* qe, Node n, int argIndex );
public:
  /** the data */
  std::map< Node, TermArgTrie > d_data;
public:
  bool addTerm( QuantifiersEngine* qe, Node n ) { return addTerm2( qe, n, 0 ); }
};/* class TermArgTrie */

class TermDb {
private:
  /** reference to the quantifiers engine */
  QuantifiersEngine* d_quantEngine;
  /** calculated no match terms */
  bool d_matching_active;
  /** terms processed */
  std::map< Node, bool > d_processed;
public:
  TermDb( QuantifiersEngine* qe ) : d_quantEngine( qe ), d_matching_active( true ){}
  ~TermDb(){}
  /** map from APPLY_UF operators to ground terms for that operator */
  std::map< Node, std::vector< Node > > d_op_map;
  /** map from APPLY_UF functions to trie */
  std::map< Node, TermArgTrie > d_func_map_trie;
  /** map from APPLY_UF predicates to trie */
  std::map< Node, TermArgTrie > d_pred_map_trie[2];
  /** map from type nodes to terms of that type */
  std::map< TypeNode, std::vector< Node > > d_type_map;
  /** add a term to the database */
  void addTerm( Node n, std::vector< Node >& added, bool withinQuant = false );
  /** reset (calculate which terms are active) */
  void reset( Theory::Effort effort );
  /** set active */
  void setMatchingActive( bool a ) { d_matching_active = a; }
  /** get active */
  bool getMatchingActive() { return d_matching_active; }
public:
  /** parent structure (for efficient E-matching):
      n -> op -> index -> L
      map from node "n" to a list of nodes "L", where each node n' in L
        has operator "op", and n'["index"] = n.
      for example, d_parents[n][f][1] = { f( t1, n ), f( t2, n ), ... }
  */
  std::map< Node, std::map< Node, std::map< int, std::vector< Node > > > > d_parents;
};/* class TermDb */

namespace quantifiers {
  class InstantiationEngine;
}/* CVC4::theory::quantifiers */

class QuantifiersEngine {
  friend class quantifiers::InstantiationEngine;
  friend class InstMatch;
private:
  typedef context::CDHashMap< Node, bool, NodeHashFunction > BoolMap;
  /** reference to theory engine object */
  TheoryEngine* d_te;
  /** vector of modules for quantifiers */
  std::vector< QuantifiersModule* > d_modules;
  /** equality query class */
  EqualityQuery* d_eq_query;

  /** list of all quantifiers */
  std::vector< Node > d_quants;
  /** list of quantifiers asserted in the current context */
  context::CDList<Node> d_forall_asserts;
  /** map from universal quantifiers to the list of variables */
  std::map< Node, std::vector< Node > > d_vars;
  /** map from universal quantifiers to the list of skolem constants */
  std::map< Node, std::vector< Node > > d_skolem_constants;
  /** map from universal quantifiers to their skolemized body */
  std::map< Node, Node > d_skolem_body;
  /** map from universal quantifiers to their bound body */
  std::map< Node, Node > d_bound_body;
  /** instantiation constants to universal quantifiers */
  std::map< Node, Node > d_inst_constants_map;
  /** map from universal quantifiers to their counterexample body */
  std::map< Node, Node > d_counterexample_body;
  /** map from universal quantifiers to the list of instantiation constants */
  std::map< Node, std::vector< Node > > d_inst_constants;
  /** map from quantifiers to whether they are active */
  BoolMap d_active;
  /** lemmas produced */
  std::map< Node, bool > d_lemmas_produced;
  /** lemmas waiting */
  std::vector< Node > d_lemmas_waiting;
  /** inst matches produced for each quantifier */
  std::map< Node, InstMatchTrie > d_inst_match_trie;
  /** free variable for instantiation constant type */
  std::map< TypeNode, Node > d_free_vars;
  /** owner of quantifiers */
  std::map< Node, Theory* > d_owner;
  /** term database */
  TermDb* d_term_db;
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
  /** set instantiation level attr */
  void setInstantiationLevelAttr( Node n, uint64_t level );
  /** set instantiation constant attr */
  void setInstantiationConstantAttr( Node n, Node f );
  /** make instantiation constants for */
  void makeInstantiationConstantsFor( Node f );

  KEEP_STATISTIC(TimerStat, d_time, "theory::QuantifiersEngine::time");

public:
  QuantifiersEngine(context::Context* c, TheoryEngine* te);
  ~QuantifiersEngine(){}
  /** get instantiator for id */
  Instantiator* getInstantiator( int id );
  /** get theory engine */
  TheoryEngine* getTheoryEngine() { return d_te; }
  /** get equality query object */
  EqualityQuery* getEqualityQuery() { return d_eq_query; }
  /** set equality query object */
  void setEqualityQuery( EqualityQuery* eq ) { d_eq_query = eq; }
public:
  /** add module */
  void addModule( QuantifiersModule* qm ) { d_modules.push_back( qm ); }
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
public:
  /** add lemma lem */
  bool addLemma( Node lem );
  /** instantiate f with arguments terms */
  bool addInstantiation( Node f, std::vector< Node >& terms );
  /** do instantiation specified by m */
  bool addInstantiation( Node f, InstMatch& m, bool addSplits = false );
  /** split on node n */
  bool addSplit( Node n, bool reqPhase = false, bool reqPhasePol = true );
  /** add split equality */
  bool addSplitEquality( Node n1, Node n2, bool reqPhase = false, bool reqPhasePol = true );
  /** has added lemma */
  bool hasAddedLemma() { return !d_lemmas_waiting.empty(); }
  /** flush lemmas */
  void flushLemmas( OutputChannel* out );
  /** get number of waiting lemmas */
  int getNumLemmasWaiting() { return (int)d_lemmas_waiting.size(); }
public:
  /** get number of quantifiers */
  int getNumQuantifiers() { return (int)d_quants.size(); }
  /** get quantifier */
  Node getQuantifier( int i ) { return d_quants[i]; }
  /** get number of asserted quantifiers */
  int getNumAssertedQuantifiers() { return (int)d_forall_asserts.size(); }
  /** get asserted quantifier */
  Node getAssertedQuantifier( int i ) { return d_forall_asserts[i]; }
  /** get instantiation constants */
  void getInstantiationConstantsFor( Node f, std::vector< Node >& ics ) {
    ics.insert( ics.begin(), d_inst_constants[f].begin(), d_inst_constants[f].end() );
  }
  /** get the i^th instantiation constant of f */
  Node getInstantiationConstant( Node f, int i ) { return d_inst_constants[f][i]; }
  /** get number of instantiation constants for f */
  int getNumInstantiationConstants( Node f ) { return (int)d_inst_constants[f].size(); }
  std::vector<Node> createInstVariable( std::vector<Node> & vars );
public:
  /** get the ce body f[e/x] */
  Node getCounterexampleBody( Node f );
  /** get the skolemized body f[e/x] */
  Node getSkolemizedBody( Node f );
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
  /** returns node n with bound vars of f replaced by instantiation constants of f
      node n : is the futur pattern
      node f : is the quantifier containing which bind the variable
      return a pattern where the variable are replaced by variable for
      instantiation.
   */
  Node getSubstitutedNode( Node n, Node f );
  /** same as before but node f is just linked to the new pattern by the
      applied attribute
      vars the bind variable
      nvars the same variable but with an attribute
  */
  Node convertNodeToPattern( Node n, Node f,
                             const std::vector<Node> & vars,
                             const std::vector<Node> & nvars);
  /** get free variable for instantiation constant */
  Node getFreeVariableForInstConstant( Node n );
  /** get bound variable for variable */
  Node getBoundVariableForVariable( Node n );
public:
  /** has owner */
  bool hasOwner( Node f ) { return d_owner.find( f )!=d_owner.end(); }
  /** get owner */
  Theory* getOwner( Node f ) { return d_owner[f]; }
  /** set owner */
  void setOwner( Node f, Theory* t ) { d_owner[f] = t; }
public:
  /** get term database */
  TermDb* getTermDatabase() { return d_term_db; }
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
    Statistics();
    ~Statistics();
  };/* class QuantifiersEngine::Statistics */
  Statistics d_statistics;
};/* class QuantifiersEngine */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS_ENGINE_H */
