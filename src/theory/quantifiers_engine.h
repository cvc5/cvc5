/*********************                                                        */
/*! \file quantifiers_engine.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Theory instantiator, Instantiation Engine classes
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS_ENGINE_H
#define __CVC4__THEORY__QUANTIFIERS_ENGINE_H

#include <iosfwd>
#include <map>
#include <unordered_map>

#include "context/cdchunk_list.h"
#include "context/cdhashset.h"
#include "options/quantifiers_modes.h"
#include "theory/quantifiers/inst_match.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/theory.h"
#include "util/hash.h"
#include "util/statistics_registry.h"

namespace CVC4 {

class TheoryEngine;

namespace theory {

class QuantifiersEngine;

class InstantiationNotify {
public:
  InstantiationNotify(){}
  virtual ~InstantiationNotify() {}
  virtual bool notifyInstantiation( unsigned quant_e, Node q, Node lem, std::vector< Node >& terms, Node body ) = 0;
  virtual void filterInstantiations() = 0;
};

namespace quantifiers {
  class TermDb;
  class TermDbSygus;
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
  class AlphaEquivalence;
  class FunDefEngine;
  class QuantEqualityEngine;
  class FullSaturation;
  class InstStrategyCbqi;
  class InstStrategyCegqi;
  class QuantDSplit;
  class QuantAntiSkolem;
  class EqualityInference;
  class InstPropagator;
}/* CVC4::theory::quantifiers */

namespace inst {
  class TriggerTrie;
}/* CVC4::theory::inst */

//class EfficientEMatcher;
class EqualityQueryQuantifiersEngine;

class QuantifiersEngine {
  friend class quantifiers::InstantiationEngine;
  friend class quantifiers::InstStrategyCbqi;
  friend class quantifiers::InstStrategyCegqi;
  friend class quantifiers::ModelEngine;
  friend class quantifiers::RewriteEngine;
  friend class quantifiers::QuantConflictFind;
  friend class inst::InstMatch;
  typedef context::CDHashMap< Node, bool, NodeHashFunction > BoolMap;
  typedef context::CDChunkList<Node> NodeList;
  typedef context::CDChunkList<bool> BoolList;
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;
private:
  /** reference to theory engine object */
  TheoryEngine* d_te;
  /** vector of utilities for quantifiers */
  std::vector< QuantifiersUtil* > d_util;
  /** vector of modules for quantifiers */
  std::vector< QuantifiersModule* > d_modules;
  /** instantiation notify */
  std::vector< InstantiationNotify* > d_inst_notify;
  /** equality query class */
  EqualityQueryQuantifiersEngine* d_eq_query;
  /** for computing relevance of quantifiers */
  QuantRelevance * d_quant_rel;
  /** relevant domain */
  quantifiers::RelevantDomain* d_rel_dom;
  /** alpha equivalence */
  quantifiers::AlphaEquivalence * d_alpha_equiv;
  /** model builder */
  quantifiers::QModelBuilder* d_builder;
  /** utility for effectively propositional logic */
  QuantEPR * d_qepr;
private:
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
  /** function definitions engine */
  quantifiers::FunDefEngine * d_fun_def_engine;
  /** quantifiers equality engine */
  quantifiers::QuantEqualityEngine * d_uee;
  /** full saturation */
  quantifiers::FullSaturation * d_fs;
  /** counterexample-based quantifier instantiation */
  quantifiers::InstStrategyCbqi * d_i_cbqi;
  /** quantifiers splitting */
  quantifiers::QuantDSplit * d_qsplit;
  /** quantifiers anti-skolemization */
  quantifiers::QuantAntiSkolem * d_anti_skolem;
  /** quantifiers instantiation propagtor */
  quantifiers::InstPropagator * d_inst_prop;
public: //effort levels
  enum {
    QEFFORT_CONFLICT,
    QEFFORT_STANDARD,
    QEFFORT_MODEL,
    QEFFORT_LAST_CALL,
    //none
    QEFFORT_NONE,
  };
private:  //this information is reset during check
  /** current effort level */
  unsigned d_curr_effort_level;
  /** are we in conflict */
  bool d_conflict;
  context::CDO< bool > d_conflict_c;
  /** has added lemma this round */
  bool d_hasAddedLemma;
  /** whether to use model equality engine */
  bool d_useModelEe;
private:
  /** list of all quantifiers seen */
  std::map< Node, bool > d_quants;
  /** quantifiers reduced */
  BoolMap d_quants_red;
  std::map< Node, Node > d_quants_red_lem;
  /** list of all lemmas produced */
  //std::map< Node, bool > d_lemmas_produced;
  BoolMap d_lemmas_produced_c;
  /** lemmas waiting */
  std::vector< Node > d_lemmas_waiting;
  /** phase requirements waiting */
  std::map< Node, bool > d_phase_req_waiting;
  /** list of all instantiations produced for each quantifier */
  std::map< Node, inst::InstMatchTrie > d_inst_match_trie;
  std::map< Node, inst::CDInstMatchTrie* > d_c_inst_match_trie;
  /** recorded instantiations */
  std::vector< std::pair< Node, std::vector< Node > > > d_recorded_inst;
  /** quantifiers that have been skolemized */
  BoolMap d_skolemized;
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
  /** inst round counters TODO: make context-dependent? */
  context::CDO< int > d_ierCounter_c;
  int d_ierCounter;
  int d_ierCounter_lc;
  int d_ierCounterLastLc;
  int d_inst_when_phase;
  /** has presolve been called */
  context::CDO< bool > d_presolve;
  /** presolve cache */
  NodeSet d_presolve_in;
  NodeList d_presolve_cache;
  BoolList d_presolve_cache_wq;
  BoolList d_presolve_cache_wic;

public:
  QuantifiersEngine(context::Context* c, context::UserContext* u, TheoryEngine* te);
  ~QuantifiersEngine();
  /** get theory engine */
  TheoryEngine* getTheoryEngine() { return d_te; }
  /** get equality query */
  EqualityQueryQuantifiersEngine* getEqualityQuery();
  /** get default sat context for quantifiers engine */
  context::Context* getSatContext();
  /** get default sat context for quantifiers engine */
  context::UserContext* getUserContext();
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
  /** get utility for EPR */
  QuantEPR* getQuantEPR() { return d_qepr; }
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
  /** function definition engine */
  quantifiers::FunDefEngine * getFunDefEngine() { return d_fun_def_engine; }
  /** quantifiers equality engine */
  quantifiers::QuantEqualityEngine * getQuantEqualityEngine() { return d_uee; }
  /** get full saturation */
  quantifiers::FullSaturation * getFullSaturation() { return d_fs; }
  /** get inst strategy cbqi */
  quantifiers::InstStrategyCbqi * getInstStrategyCbqi() { return d_i_cbqi; }
  /** get quantifiers splitting */
  quantifiers::QuantDSplit * getQuantDSplit() { return d_qsplit; }
  /** get quantifiers anti-skolemization */
  quantifiers::QuantAntiSkolem * getQuantAntiSkolem() { return d_anti_skolem; }
private:
  /** owner of quantified formulas */
  std::map< Node, QuantifiersModule * > d_owner;
  std::map< Node, int > d_owner_priority;
public:
  /** get owner */
  QuantifiersModule * getOwner( Node q );
  /** set owner */
  void setOwner( Node q, QuantifiersModule * m, int priority = 0 );
  /** considers */
  bool hasOwnership( Node q, QuantifiersModule * m = NULL );
  /** is finite bound */
  bool isFiniteBound( Node q, Node v );
public:
  /** initialize */
  void finishInit();
  /** presolve */
  void presolve();
  /** notify preprocessed assertion */
  void ppNotifyAssertions(const std::vector<Node>& assertions);
  /** check at level */
  void check( Theory::Effort e );
  /** notify that theories were combined */
  void notifyCombineTheories();
  /** register quantifier */
  bool registerQuantifier( Node f );
  /** register quantifier */
  void registerPattern( std::vector<Node> & pattern);
  /** assert universal quantifier */
  void assertQuantifier( Node q, bool pol );
  /** propagate */
  void propagate( Theory::Effort level );
  /** get next decision request */
  Node getNextDecisionRequest( unsigned& priority );
private:
  /** reduceQuantifier, return true if reduced */
  bool reduceQuantifier( Node q );
  /** compute term vector */
  void computeTermVector( Node f, InstMatch& m, std::vector< Node >& vars, std::vector< Node >& terms );
  /** record instantiation, return true if it was non-duplicate */
  bool recordInstantiationInternal( Node q, std::vector< Node >& terms, bool modEq = false, bool addedLem = true );
  /** remove instantiation */
  bool removeInstantiationInternal( Node q, std::vector< Node >& terms );
  /** set instantiation level attr */
  static void setInstantiationLevelAttr( Node n, Node qn, uint64_t level );
  /** flush lemmas */
  void flushLemmas();
public:
  /** get instantiation */
  Node getInstantiation( Node q, std::vector< Node >& vars, std::vector< Node >& terms, bool doVts = false );
  /** get instantiation */
  Node getInstantiation( Node q, InstMatch& m, bool doVts = false );
  /** get instantiation */
  Node getInstantiation( Node q, std::vector< Node >& terms, bool doVts = false );
  /** do substitution */
  Node getSubstitute( Node n, std::vector< Node >& terms, std::map< Node, Node >& visited );
  /** add lemma lem */
  bool addLemma( Node lem, bool doCache = true, bool doRewrite = true );
  /** remove pending lemma */
  bool removeLemma( Node lem );
  /** add require phase */
  void addRequirePhase( Node lit, bool req );
  /** do instantiation specified by m */
  bool addInstantiation( Node q, InstMatch& m, bool mkRep = false, bool modEq = false, bool doVts = false );
  /** add instantiation */
  bool addInstantiation( Node q, std::vector< Node >& terms, bool mkRep = false, bool modEq = false, bool doVts = false );
  /** remove pending instantiation */
  bool removeInstantiation( Node q, Node lem, std::vector< Node >& terms );
  /** split on node n */
  bool addSplit( Node n, bool reqPhase = false, bool reqPhasePol = true );
  /** add split equality */
  bool addSplitEquality( Node n1, Node n2, bool reqPhase = false, bool reqPhasePol = true );
  /** add EPR axiom */
  bool addEPRAxiom( TypeNode tn );
  /** mark relevant quantified formula, this will indicate it should be checked before the others */
  void markRelevant( Node q );
  /** has added lemma */
  bool hasAddedLemma() { return !d_lemmas_waiting.empty() || d_hasAddedLemma; }
  /** is in conflict */
  bool inConflict() { return d_conflict; }
  /** set conflict */
  void setConflict();
  /** get number of waiting lemmas */
  unsigned getNumLemmasWaiting() { return d_lemmas_waiting.size(); }
  /** get needs check */
  bool getInstWhenNeedsCheck( Theory::Effort e );
  /** get user pat mode */
  quantifiers::UserPatMode getInstUserPatMode();
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
  /** notification when master equality engine is updated */
  void eqNotifyNewClass(TNode t);
  void eqNotifyPreMerge(TNode t1, TNode t2);
  void eqNotifyPostMerge(TNode t1, TNode t2);
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);
  /** get the master equality engine */
  eq::EqualityEngine* getMasterEqualityEngine();
  /** get the active equality engine */
  eq::EqualityEngine* getActiveEqualityEngine();
  /** debug print equality engine */
  void debugPrintEqualityEngine( const char * c );
  /** get internal representative */
  Node getInternalRepresentative( Node a, Node q, int index );
public:
  /** print instantiations */
  void printInstantiations( std::ostream& out );
  /** print solution for synthesis conjectures */
  void printSynthSolution( std::ostream& out );
  /** get list of quantified formulas that were instantiated */
  void getInstantiatedQuantifiedFormulas( std::vector< Node >& qs );
  /** get instantiations */
  void getInstantiations( Node q, std::vector< Node >& insts );
  void getInstantiations( std::map< Node, std::vector< Node > >& insts );
  /** get instantiation term vectors */
  void getInstantiationTermVectors( Node q, std::vector< std::vector< Node > >& tvecs );
  void getInstantiationTermVectors( std::map< Node, std::vector< std::vector< Node > > >& insts );
  /** get instantiated conjunction */
  Node getInstantiatedConjunction( Node q );
  /** get unsat core lemmas */
  bool getUnsatCoreLemmas( std::vector< Node >& active_lemmas );
  bool getUnsatCoreLemmas( std::vector< Node >& active_lemmas, std::map< Node, Node >& weak_imp );
  /** get inst for lemmas */
  void getExplanationForInstLemmas( std::vector< Node >& lems, std::map< Node, Node >& quant, std::map< Node, std::vector< Node > >& tvec ); 
  /** statistics class */
  class Statistics {
  public:
    TimerStat d_time;
    TimerStat d_qcf_time;
    TimerStat d_ematching_time;
    IntStat d_num_quant;
    IntStat d_instantiation_rounds;
    IntStat d_instantiation_rounds_lc;
    IntStat d_instantiations;
    IntStat d_inst_duplicate;
    IntStat d_inst_duplicate_eq;
    IntStat d_inst_duplicate_ent;
    IntStat d_inst_duplicate_model_true;
    IntStat d_triggers;
    IntStat d_simple_triggers;
    IntStat d_multi_triggers;
    IntStat d_multi_trigger_instantiations;
    IntStat d_red_alpha_equiv;
    IntStat d_instantiations_user_patterns;
    IntStat d_instantiations_auto_gen;
    IntStat d_instantiations_guess;
    IntStat d_instantiations_qcf;
    IntStat d_instantiations_qcf_prop;
    IntStat d_instantiations_fmf_exh;
    IntStat d_instantiations_fmf_mbqi;
    IntStat d_instantiations_cbqi;
    IntStat d_instantiations_rr;
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
  /** quantifiers equality inference */
  quantifiers::EqualityInference * d_eq_inference;
  context::CDO< unsigned > d_eqi_counter;
  /** internal representatives */
  std::map< TypeNode, std::map< Node, Node > > d_int_rep;
  /** rep score */
  std::map< Node, int > d_rep_score;
  /** reset count */
  int d_reset_count;

  /** processInferences : will merge equivalence classes in master equality engine, if possible */
  bool processInferences( Theory::Effort e );
  /** node contains */
  Node getInstance( Node n, const std::vector< Node >& eqc, std::unordered_map<TNode, Node, TNodeHashFunction>& cache );
  /** get score */
  int getRepScore( Node n, Node f, int index, TypeNode v_tn );
  /** flatten representatives */
  void flattenRepresentatives( std::map< TypeNode, std::vector< Node > >& reps );
public:
  EqualityQueryQuantifiersEngine( context::Context* c, QuantifiersEngine* qe );
  virtual ~EqualityQueryQuantifiersEngine();
  /** reset */
  bool reset( Theory::Effort e );
  /** identify */
  std::string identify() const { return "EqualityQueryQE"; }
  /** general queries about equality */
  bool hasTerm( Node a );
  Node getRepresentative( Node a );
  bool areEqual( Node a, Node b );
  bool areDisequal( Node a, Node b );
  eq::EqualityEngine* getEngine();
  void getEquivalenceClass( Node a, std::vector< Node >& eqc );
  TNode getCongruentTerm( Node f, std::vector< TNode >& args );
  /** getInternalRepresentative gets the current best representative in the equivalence class of a, based on some criteria.
      If cbqi is active, this will return a term in the equivalence class of "a" that does
      not contain instantiation constants, if such a term exists.
   */
  Node getInternalRepresentative( Node a, Node f, int index );
  /** get quantifiers equality inference */
  quantifiers::EqualityInference * getEqualityInference() { return d_eq_inference; }
}; /* EqualityQueryQuantifiersEngine */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS_ENGINE_H */
