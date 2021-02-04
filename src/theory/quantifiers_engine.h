/*********************                                                        */
/*! \file quantifiers_engine.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Theory instantiator, Instantiation Engine classes
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS_ENGINE_H
#define CVC4__THEORY__QUANTIFIERS_ENGINE_H

#include <map>
#include <unordered_map>

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "expr/attribute.h"
#include "theory/quantifiers/ematching/trigger_trie.h"
#include "theory/quantifiers/equality_query.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/fmf/model_builder.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/skolemize.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_enumeration.h"
#include "theory/quantifiers/term_util.h"
#include "util/statistics_registry.h"

namespace CVC4 {

class TheoryEngine;

namespace theory {

class DecisionManager;

namespace quantifiers {
class QuantifiersModules;
}

// TODO: organize this more/review this, github issue #1163
class QuantifiersEngine {
  friend class ::CVC4::TheoryEngine;
  typedef context::CDHashMap< Node, bool, NodeHashFunction > BoolMap;
  typedef context::CDList<Node> NodeList;
  typedef context::CDList<bool> BoolList;
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

 public:
  QuantifiersEngine(quantifiers::QuantifiersState& qstate,
                    quantifiers::QuantifiersInferenceManager& qim,
                    ProofNodeManager* pnm);
  ~QuantifiersEngine();
  //---------------------- external interface
  /** get theory engine */
  TheoryEngine* getTheoryEngine() const;
  /** Get the decision manager */
  DecisionManager* getDecisionManager();
  /** get default output channel for the quantifiers engine */
  OutputChannel& getOutputChannel();
  /** get default valuation for the quantifiers engine */
  Valuation& getValuation();
  /** The quantifiers state object */
  quantifiers::QuantifiersState& getState();
  /** The quantifiers inference manager */
  quantifiers::QuantifiersInferenceManager& getInferenceManager();
  //---------------------- end external interface
  //---------------------- utilities
  /** get the model builder */
  quantifiers::QModelBuilder* getModelBuilder() const;
  /** get model */
  quantifiers::FirstOrderModel* getModel() const;
  /** get term database */
  quantifiers::TermDb* getTermDatabase() const;
  /** get term database sygus */
  quantifiers::TermDbSygus* getTermDatabaseSygus() const;
  /** get term utilities */
  quantifiers::TermUtil* getTermUtil() const;
  /** get quantifiers attributes */
  quantifiers::QuantAttributes* getQuantAttributes() const;
  /** get instantiate utility */
  quantifiers::Instantiate* getInstantiate() const;
  /** get skolemize utility */
  quantifiers::Skolemize* getSkolemize() const;
  /** get term enumeration utility */
  quantifiers::TermEnumeration* getTermEnumeration() const;
  /** get trigger database */
  inst::TriggerTrie* getTriggerDatabase() const;
  //---------------------- end utilities
 private:
  //---------------------- private initialization
  /**
   * Finish initialize, which passes pointers to the objects that quantifiers
   * engine needs but were not available when it was created. This is
   * called after theories have been created but before they have finished
   * initialization.
   *
   * @param te The theory engine
   * @param dm The decision manager of the theory engine
   */
  void finishInit(TheoryEngine* te, DecisionManager* dm);
  //---------------------- end private initialization
 public:
  /** does variable v of quantified formula q have a finite bound? */
  bool isFiniteBound(Node q, Node v) const;
  /** get bound var type
   *
   * This returns the type of bound that was inferred for variable v of
   * quantified formula q.
   */
  BoundVarType getBoundVarType(Node q, Node v) const;
  /**
   * Get the indices of bound variables, in the order they should be processed
   * in a RepSetIterator.
   *
   * For details, see BoundedIntegers::getBoundVarIndices.
   */
  void getBoundVarIndices(Node q, std::vector<unsigned>& indices) const;
  /**
   * Get bound elements
   *
   * This gets the (finite) enumeration of the range of variable v of quantified
   * formula q and adds it into the vector elements in the context of the
   * iteration being performed by rsi. It returns true if it could successfully
   * determine this range.
   *
   * For details, see BoundedIntegers::getBoundElements.
   */
  bool getBoundElements(RepSetIterator* rsi,
                        bool initial,
                        Node q,
                        Node v,
                        std::vector<Node>& elements) const;

 public:
  /** presolve */
  void presolve();
  /** notify preprocessed assertion */
  void ppNotifyAssertions(const std::vector<Node>& assertions);
  /** check at level */
  void check( Theory::Effort e );
  /** notify that theories were combined */
  void notifyCombineTheories();
  /** preRegister quantifier
   *
   * This function is called after registerQuantifier for quantified formulas
   * that are pre-registered to the quantifiers theory.
   */
  void preRegisterQuantifier(Node q);
  /** assert universal quantifier */
  void assertQuantifier( Node q, bool pol );
private:
 /** (context-indepentent) register quantifier internal
  *
  * This is called when a quantified formula q is pre-registered to the
  * quantifiers theory, and updates the modules in this class with
  * context-independent information about how to handle q. This includes basic
  * information such as which module owns q.
  */
 void registerQuantifierInternal(Node q);
 /** reduceQuantifier, return true if reduced */
 bool reduceQuantifier(Node q);
 /** flush lemmas */
 void flushLemmas();

public:
 /**
  * Add lemma to the lemma buffer of this quantifiers engine.
  * @param lem The lemma to send
  * @param doCache Whether to cache the lemma (to check for duplicate lemmas)
  * @param doRewrite Whether to rewrite the lemma
  * @return true if the lemma was successfully added to the buffer
  */
 bool addLemma(Node lem, bool doCache = true, bool doRewrite = true);
 /**
  * Add trusted lemma lem, same as above, but where a proof generator may be
  * provided along with the lemma.
  */
 bool addTrustedLemma(TrustNode tlem,
                      bool doCache = true,
                      bool doRewrite = true);
 /** remove pending lemma */
 bool removeLemma(Node lem);
 /** add require phase */
 void addRequirePhase(Node lit, bool req);
 /** mark relevant quantified formula, this will indicate it should be checked
  * before the others */
 void markRelevant(Node q);
 /** has added lemma */
 bool hasAddedLemma() const;
 /** get current q effort */
 QuantifiersModule::QEffort getCurrentQEffort() { return d_curr_effort_level; }
 /** get number of waiting lemmas */
 unsigned getNumLemmasWaiting() { return d_lemmas_waiting.size(); }
 /** get needs check */
 bool getInstWhenNeedsCheck(Theory::Effort e);
 /** get user pat mode */
 options::UserPatMode getInstUserPatMode();

public:
 /** add term to database */
 void addTermToDatabase(Node n,
                        bool withinQuant = false,
                        bool withinInstClosure = false);
 /** notification when master equality engine is updated */
 void eqNotifyNewClass(TNode t);
 /** debug print equality engine */
 void debugPrintEqualityEngine(const char* c);
 /** get internal representative
  *
  * Choose a term that is equivalent to a in the current context that is the
  * best term for instantiating the index^th variable of quantified formula q.
  * If no legal term can be found, we return null. This can occur if:
  * - a's type is not a subtype of the type of the index^th variable of q,
  * - a is in an equivalent class with all terms that are restricted not to
  * appear in instantiations of q, e.g. INST_CONSTANT terms for counterexample
  * guided instantiation.
  */
 Node getInternalRepresentative(Node a, Node q, int index);
 /**
  * Get quantifiers name, which returns a variable corresponding to the name of
  * quantified formula q if q has a name, or otherwise returns q itself.
  */
 Node getNameForQuant(Node q) const;
 /**
  * Get name for quantified formula. Returns true if q has a name or if req
  * is false. Sets name to the result of the above method.
  */
 bool getNameForQuant(Node q, Node& name, bool req = true) const;

public:
 //----------user interface for instantiations (see quantifiers/instantiate.h)
 /** print solution for synthesis conjectures */
 void printSynthSolution(std::ostream& out);
 /** get list of quantified formulas that were instantiated */
 void getInstantiatedQuantifiedFormulas(std::vector<Node>& qs);
 /** get instantiation term vectors */
 void getInstantiationTermVectors(Node q,
                                  std::vector<std::vector<Node> >& tvecs);
 void getInstantiationTermVectors(
     std::map<Node, std::vector<std::vector<Node> > >& insts);
 /**
  * Get skolemization vectors, where for each quantified formula that was
  * skolemized, this is the list of skolems that were used to witness the
  * negation of that quantified formula.
  */
 void getSkolemTermVectors(std::map<Node, std::vector<Node> >& sks) const;

 /** get synth solutions
  *
  * This method returns true if there is a synthesis solution available. This
  * is the case if the last call to check satisfiability originated in a
  * check-synth call, and the synthesis engine module of this class
  * successfully found a solution for all active synthesis conjectures.
  *
  * This method adds entries to sol_map that map functions-to-synthesize with
  * their solutions, for all active conjectures. This should be called
  * immediately after the solver answers unsat for sygus input.
  *
  * For details on what is added to sol_map, see
  * SynthConjecture::getSynthSolutions.
  */
 bool getSynthSolutions(std::map<Node, std::map<Node, Node> >& sol_map);

 //----------end user interface for instantiations

 /** statistics class */
 class Statistics
 {
  public:
    TimerStat d_time;
    TimerStat d_qcf_time;
    TimerStat d_ematching_time;
    IntStat d_num_quant;
    IntStat d_instantiation_rounds;
    IntStat d_instantiation_rounds_lc;
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

 private:
  /** The quantifiers state object */
  quantifiers::QuantifiersState& d_qstate;
  /** The quantifiers inference manager */
  quantifiers::QuantifiersInferenceManager& d_qim;
  /** Pointer to theory engine object */
  TheoryEngine* d_te;
  /** Reference to the decision manager of the theory engine */
  DecisionManager* d_decManager;
  /** vector of utilities for quantifiers */
  std::vector<QuantifiersUtil*> d_util;
  /** vector of modules for quantifiers */
  std::vector<QuantifiersModule*> d_modules;
  //------------- quantifiers utilities
  /** The quantifiers registry */
  quantifiers::QuantifiersRegistry d_qreg;
  /** all triggers will be stored in this trie */
  std::unique_ptr<inst::TriggerTrie> d_tr_trie;
  /** extended model object */
  std::unique_ptr<quantifiers::FirstOrderModel> d_model;
  /** model builder */
  std::unique_ptr<quantifiers::QModelBuilder> d_builder;
  /** term utilities */
  std::unique_ptr<quantifiers::TermUtil> d_term_util;
  /** term database */
  std::unique_ptr<quantifiers::TermDb> d_term_db;
  /** equality query class */
  std::unique_ptr<quantifiers::EqualityQueryQuantifiersEngine> d_eq_query;
  /** sygus term database */
  std::unique_ptr<quantifiers::TermDbSygus> d_sygus_tdb;
  /** quantifiers attributes */
  std::unique_ptr<quantifiers::QuantAttributes> d_quant_attr;
  /** instantiate utility */
  std::unique_ptr<quantifiers::Instantiate> d_instantiate;
  /** skolemize utility */
  std::unique_ptr<quantifiers::Skolemize> d_skolemize;
  /** term enumeration utility */
  std::unique_ptr<quantifiers::TermEnumeration> d_term_enum;
  //------------- end quantifiers utilities
  /**
   * The modules utility, which contains all of the quantifiers modules.
   */
  std::unique_ptr<quantifiers::QuantifiersModules> d_qmodules;
  //------------- temporary information during check
  /** current effort level */
  QuantifiersModule::QEffort d_curr_effort_level;
  /** has added lemma this round */
  bool d_hasAddedLemma;
  //------------- end temporary information during check
 private:
  /** list of all quantifiers seen */
  std::map<Node, bool> d_quants;
  /** quantifiers pre-registered */
  NodeSet d_quants_prereg;
  /** quantifiers reduced */
  BoolMap d_quants_red;
  std::map<Node, Node> d_quants_red_lem;
  /** list of all lemmas produced */
  // std::map< Node, bool > d_lemmas_produced;
  BoolMap d_lemmas_produced_c;
  /** lemmas waiting */
  std::vector<Node> d_lemmas_waiting;
  /** map from waiting lemmas to their proof generators */
  std::map<Node, ProofGenerator*> d_lemmasWaitingPg;
  /** phase requirements waiting */
  std::map<Node, bool> d_phase_req_waiting;
  /** inst round counters TODO: make context-dependent? */
  context::CDO<int> d_ierCounter_c;
  int d_ierCounter;
  int d_ierCounter_lc;
  int d_ierCounterLastLc;
  int d_inst_when_phase;
  /** has presolve been called */
  context::CDO<bool> d_presolve;
  /** presolve cache */
  NodeSet d_presolve_in;
  NodeList d_presolve_cache;
  BoolList d_presolve_cache_wq;
  BoolList d_presolve_cache_wic;
};/* class QuantifiersEngine */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS_ENGINE_H */
