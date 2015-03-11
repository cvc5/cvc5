/*********************                                                        */
/*! \file quantifiers_engine.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): Francois Bobot
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
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
#include "theory/quantifiers/quant_util.h"
#include "expr/attribute.h"

#include "util/statistics_registry.h"

#include <ext/hash_set>
#include <iostream>
#include <map>

namespace CVC4 {

class TheoryEngine;

namespace theory {

class QuantifiersEngine;

namespace quantifiers {
  class TermDb;
  class TermDbSygus;
}

class QuantifiersModule {
protected:
  QuantifiersEngine* d_quantEngine;
public:
  QuantifiersModule( QuantifiersEngine* qe ) : d_quantEngine( qe ){}
  virtual ~QuantifiersModule(){}
  //get quantifiers engine
  QuantifiersEngine* getQuantifiersEngine() { return d_quantEngine; }
  /** initialize */
  virtual void finishInit() {}
  /* whether this module needs to check this round */
  virtual bool needsCheck( Theory::Effort e ) { return e>=Theory::EFFORT_LAST_CALL; }
  /* whether this module needs a model built */
  virtual bool needsModel( Theory::Effort e ) { return false; }
  /* whether this module needs a model built */
  virtual bool needsFullModel( Theory::Effort e ) { return false; }
  /* reset at a round */
  virtual void reset_round( Theory::Effort e ){}
  /* Call during quantifier engine's check */
  virtual void check( Theory::Effort e, unsigned quant_e ) = 0;
  /* Called for new quantifiers */
  virtual void registerQuantifier( Node q ) = 0;
  virtual void assertNode( Node n ) = 0;
  virtual void propagate( Theory::Effort level ){}
  virtual Node getNextDecisionRequest() { return TNode::null(); }
  virtual Node explain(TNode n) { return TNode::null(); }
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  virtual std::string identify() const = 0;
public:
  eq::EqualityEngine * getEqualityEngine();
  bool areDisequal( TNode n1, TNode n2 );
  bool areEqual( TNode n1, TNode n2 );
  TNode getRepresentative( TNode n );
  quantifiers::TermDb * getTermDatabase();
};/* class QuantifiersModule */

namespace quantifiers {
  class FirstOrderModel;
  //modules
  class InstantiationEngine;
  class ModelEngine;
  class BoundedIntegers;
  class QuantConflictFind;
  class RewriteEngine;
  class RelevantDomain;
  class QModelBuilder;
  class ConjectureGenerator;
  class CegInstantiation;
  class LtePartialInst;
}/* CVC4::theory::quantifiers */

namespace inst {
  class TriggerTrie;
}/* CVC4::theory::inst */

//class EfficientEMatcher;
class EqualityQueryQuantifiersEngine;

class QuantifiersEngine {
  friend class quantifiers::InstantiationEngine;
  friend class quantifiers::ModelEngine;
  friend class quantifiers::RewriteEngine;
  friend class quantifiers::QuantConflictFind;
  friend class inst::InstMatch;
private:
  typedef context::CDHashMap< Node, bool, NodeHashFunction > BoolMap;
  /** reference to theory engine object */
  TheoryEngine* d_te;
  /** vector of modules for quantifiers */
  std::vector< QuantifiersModule* > d_modules;
  /** equality query class */
  EqualityQueryQuantifiersEngine* d_eq_query;
  /** for computing relevance of quantifiers */
  QuantRelevance * d_quant_rel;
  /** relevant domain */
  quantifiers::RelevantDomain* d_rel_dom;
  /** model builder */
  quantifiers::QModelBuilder* d_builder;
  /** phase requirements for each quantifier for each instantiation literal */
  std::map< Node, QuantPhaseReq* > d_phase_reqs;
  /** instantiation engine */
  quantifiers::InstantiationEngine* d_inst_engine;
  /** model engine */
  quantifiers::ModelEngine* d_model_engine;
  /** bounded integers utility */
  quantifiers::BoundedIntegers * d_bint;
  /** Conflict find mechanism for quantifiers */
  quantifiers::QuantConflictFind* d_qcf;
  /** rewrite rules utility */
  quantifiers::RewriteEngine * d_rr_engine;
  /** subgoal generator */
  quantifiers::ConjectureGenerator * d_sg_gen;
  /** ceg instantiation */
  quantifiers::CegInstantiation * d_ceg_inst;
  /** lte partial instantiation */
  quantifiers::LtePartialInst * d_lte_part_inst;
public: //effort levels
  enum {
    QEFFORT_CONFLICT,
    QEFFORT_STANDARD,
    QEFFORT_MODEL,
  };
private:
  /** list of all quantifiers seen */
  std::map< Node, bool > d_quants;
  /** list of all lemmas produced */
  //std::map< Node, bool > d_lemmas_produced;
  BoolMap d_lemmas_produced_c;
  /** lemmas waiting */
  std::vector< Node > d_lemmas_waiting;
  /** phase requirements waiting */
  std::map< Node, bool > d_phase_req_waiting;
  /** has added lemma this round */
  bool d_hasAddedLemma;
  /** has a conflict been found */
  bool d_conflict;
  /** list of all instantiations produced for each quantifier */
  std::map< Node, inst::InstMatchTrie > d_inst_match_trie;
  std::map< Node, inst::CDInstMatchTrie* > d_c_inst_match_trie;
  /** quantifiers that have been skolemized */
  std::map< Node, bool > d_skolemized;
  /** term database */
  quantifiers::TermDb* d_term_db;
  /** all triggers will be stored in this trie */
  inst::TriggerTrie* d_tr_trie;
  /** extended model object */
  quantifiers::FirstOrderModel* d_model;
  /** statistics for debugging */
  std::map< Node, int > d_total_inst_debug;
  std::map< Node, int > d_temp_inst_debug;
  int d_total_inst_count_debug;
  /** inst round counters */
  int d_ierCounter;
  int d_ierCounter_lc;
private:
  KEEP_STATISTIC(TimerStat, d_time, "theory::QuantifiersEngine::time");
public:
  QuantifiersEngine(context::Context* c, context::UserContext* u, TheoryEngine* te);
  ~QuantifiersEngine();
  /** get theory engine */
  TheoryEngine* getTheoryEngine() { return d_te; }
  /** get equality query object for the given type. The default is the
      generic one */
  EqualityQueryQuantifiersEngine* getEqualityQuery();
  /** get default sat context for quantifiers engine */
  context::Context* getSatContext();
  /** get default sat context for quantifiers engine */
  context::Context* getUserContext();
  /** get default output channel for the quantifiers engine */
  OutputChannel& getOutputChannel();
  /** get default valuation for the quantifiers engine */
  Valuation& getValuation();
  /** get relevant domain */
  quantifiers::RelevantDomain* getRelevantDomain() { return d_rel_dom; }
  /** get quantifier relevance */
  QuantRelevance* getQuantifierRelevance() { return d_quant_rel; }
  /** get the model builder */
  quantifiers::QModelBuilder* getModelBuilder() { return d_builder; }
  /** get phase requirement information */
  QuantPhaseReq* getPhaseRequirements( Node f ) { return d_phase_reqs.find( f )==d_phase_reqs.end() ? NULL : d_phase_reqs[f]; }
  /** get phase requirement terms */
  void getPhaseReqTerms( Node f, std::vector< Node >& nodes );
public:  //modules
  /** get instantiation engine */
  quantifiers::InstantiationEngine* getInstantiationEngine() { return d_inst_engine; }
  /** get model engine */
  quantifiers::ModelEngine* getModelEngine() { return d_model_engine; }
  /** get bounded integers utility */
  quantifiers::BoundedIntegers * getBoundedIntegers() { return d_bint; }
  /** Conflict find mechanism for quantifiers */
  quantifiers::QuantConflictFind* getConflictFind() { return d_qcf; }
  /** rewrite rules utility */
  quantifiers::RewriteEngine * getRewriteEngine() { return d_rr_engine; }
  /** subgoal generator */
  quantifiers::ConjectureGenerator * getConjectureGenerator() { return d_sg_gen; }
  /** ceg instantiation */
  quantifiers::CegInstantiation * getCegInstantiation() { return d_ceg_inst; }
  /** local theory ext partial inst */
  quantifiers::LtePartialInst * getLtePartialInst() { return d_lte_part_inst; }
private:
  /** owner of quantified formulas */
  std::map< Node, QuantifiersModule * > d_owner;
public:
  /** get owner */
  QuantifiersModule * getOwner( Node q );
  /** set owner */
  void setOwner( Node q, QuantifiersModule * m );
  /** considers */
  bool hasOwnership( Node q, QuantifiersModule * m = NULL );
public:
  /** initialize */
  void finishInit();
  /** check at level */
  void check( Theory::Effort e );
  /** register quantifier */
  bool registerQuantifier( Node f );
  /** register quantifier */
  void registerPattern( std::vector<Node> & pattern);
  /** assert universal quantifier */
  void assertQuantifier( Node q, bool pol );
  /** propagate */
  void propagate( Theory::Effort level );
  /** get next decision request */
  Node getNextDecisionRequest();
private:
  /** compute term vector */
  void computeTermVector( Node f, InstMatch& m, std::vector< Node >& vars, std::vector< Node >& terms );
  /** instantiate f with arguments terms */
  bool addInstantiation( Node f, std::vector< Node >& vars, std::vector< Node >& terms );
  /** set instantiation level attr */
  static void setInstantiationLevelAttr( Node n, Node qn, uint64_t level );
  /** flush lemmas */
  void flushLemmas();
public:
  /** get instantiation */
  Node getInstantiation( Node f, std::vector< Node >& vars, std::vector< Node >& terms );
  /** get instantiation */
  Node getInstantiation( Node f, InstMatch& m );
  /** get instantiation */
  Node getInstantiation( Node f, std::vector< Node >& terms );
  /** do substitution */
  Node getSubstitute( Node n, std::vector< Node >& terms );
  /** exist instantiation ? */
  //bool existsInstantiation( Node f, InstMatch& m, bool modEq = true, bool modInst = false );
  /** add lemma lem */
  bool addLemma( Node lem, bool doCache = true );
  /** add require phase */
  void addRequirePhase( Node lit, bool req );
  /** do instantiation specified by m */
  bool addInstantiation( Node f, InstMatch& m, bool mkRep = true, bool modEq = false, bool modInst = false );
  /** add instantiation */
  bool addInstantiation( Node f, std::vector< Node >& terms, bool mkRep = true, bool modEq = false, bool modInst = false );
  /** split on node n */
  bool addSplit( Node n, bool reqPhase = false, bool reqPhasePol = true );
  /** add split equality */
  bool addSplitEquality( Node n1, Node n2, bool reqPhase = false, bool reqPhasePol = true );
  /** has added lemma */
  bool hasAddedLemma() { return !d_lemmas_waiting.empty() || d_hasAddedLemma; }
  /** get number of waiting lemmas */
  int getNumLemmasWaiting() { return (int)d_lemmas_waiting.size(); }
  /** get needs check */
  bool getInstWhenNeedsCheck( Theory::Effort e );
  /** set instantiation level attr */
  static void setInstantiationLevelAttr( Node n, uint64_t level );
public:
  /** get model */
  quantifiers::FirstOrderModel* getModel() { return d_model; }
  /** get term database */
  quantifiers::TermDb* getTermDatabase() { return d_term_db; }
  /** get term database sygus */
  quantifiers::TermDbSygus* getTermDatabaseSygus();
  /** get trigger database */
  inst::TriggerTrie* getTriggerDatabase() { return d_tr_trie; }
  /** add term to database */
  void addTermToDatabase( Node n, bool withinQuant = false, bool withinInstClosure = false );
  /** get the master equality engine */
  eq::EqualityEngine* getMasterEqualityEngine() ;
  /** debug print equality engine */
  void debugPrintEqualityEngine( const char * c );
public:
  /** print instantiations */
  void printInstantiations( std::ostream& out );
  /** print solution for synthesis conjectures */
  void printSynthSolution( std::ostream& out );
  /** statistics class */
  class Statistics {
  public:
    IntStat d_num_quant;
    IntStat d_instantiation_rounds;
    IntStat d_instantiation_rounds_lc;
    IntStat d_instantiations;
    IntStat d_inst_duplicate;
    IntStat d_inst_duplicate_eq;
    IntStat d_triggers;
    IntStat d_simple_triggers;
    IntStat d_multi_triggers;
    IntStat d_multi_trigger_instantiations;
    Statistics();
    ~Statistics();
  };/* class QuantifiersEngine::Statistics */
  Statistics d_statistics;
};/* class QuantifiersEngine */



/** equality query object using theory engine */
class EqualityQueryQuantifiersEngine : public EqualityQuery
{
private:
  /** pointer to theory engine */
  QuantifiersEngine* d_qe;
  /** internal representatives */
  std::map< Node, Node > d_int_rep;
  /** rep score */
  std::map< Node, int > d_rep_score;
  /** reset count */
  int d_reset_count;

  bool d_liberal;
private:
  /** node contains */
  Node getInstance( Node n, const std::vector< Node >& eqc, std::hash_map<TNode, Node, TNodeHashFunction>& cache );
  /** get score */
  int getRepScore( Node n, Node f, int index );
public:
  EqualityQueryQuantifiersEngine( QuantifiersEngine* qe ) : d_qe( qe ), d_reset_count( 0 ), d_liberal( false ){}
  ~EqualityQueryQuantifiersEngine(){}
  /** reset */
  void reset();
  /** general queries about equality */
  bool hasTerm( Node a );
  Node getRepresentative( Node a );
  bool areEqual( Node a, Node b );
  bool areDisequal( Node a, Node b );
  eq::EqualityEngine* getEngine();
  void getEquivalenceClass( Node a, std::vector< Node >& eqc );
  /** getInternalRepresentative gets the current best representative in the equivalence class of a, based on some criteria.
      If cbqi is active, this will return a term in the equivalence class of "a" that does
      not contain instantiation constants, if such a term exists.
   */
  Node getInternalRepresentative( Node a, Node f, int index );
  /** flatten representatives */
  void flattenRepresentatives( std::map< TypeNode, std::vector< Node > >& reps );

  void setLiberal( bool l ) { d_liberal = l; }
}; /* EqualityQueryQuantifiersEngine */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS_ENGINE_H */
