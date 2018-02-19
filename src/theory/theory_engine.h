/*********************                                                        */
/*! \file theory_engine.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Dejan Jovanovic, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The theory engine
 **
 ** The theory engine.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY_ENGINE_H
#define __CVC4__THEORY_ENGINE_H

#include <deque>
#include <memory>
#include <set>
#include <unordered_map>
#include <vector>
#include <utility>

#include "base/cvc4_assert.h"
#include "context/cdhashset.h"
#include "expr/node.h"
#include "options/options.h"
#include "options/smt_options.h"
#include "prop/prop_engine.h"
#include "smt/command.h"
#include "smt_util/lemma_channels.h"
#include "theory/atom_requests.h"
#include "theory/bv/bv_to_bool.h"
#include "theory/interrupted.h"
#include "theory/rewriter.h"
#include "theory/shared_terms_database.h"
#include "theory/sort_inference.h"
#include "theory/substitutions.h"
#include "theory/term_registration_visitor.h"
#include "theory/theory.h"
#include "theory/uf/equality_engine.h"
#include "theory/valuation.h"
#include "util/hash.h"
#include "util/statistics_registry.h"
#include "util/unsafe_interrupt_exception.h"

namespace CVC4 {

class ResourceManager;
class LemmaProofRecipe;

/**
 * A pair of a theory and a node. This is used to mark the flow of
 * propagations between theories.
 */
struct NodeTheoryPair {
  Node node;
  theory::TheoryId theory;
  size_t timestamp;
  NodeTheoryPair(TNode node, theory::TheoryId theory, size_t timestamp = 0)
  : node(node), theory(theory), timestamp(timestamp) {}
  NodeTheoryPair() : theory(theory::THEORY_LAST), timestamp() {}
  // Comparison doesn't take into account the timestamp
  bool operator == (const NodeTheoryPair& pair) const {
    return node == pair.node && theory == pair.theory;
  }
};/* struct NodeTheoryPair */

struct NodeTheoryPairHashFunction {
  NodeHashFunction hashFunction;
  // Hash doesn't take into account the timestamp
  size_t operator()(const NodeTheoryPair& pair) const {
    uint64_t hash = fnv1a::fnv1a_64(NodeHashFunction()(pair.node));
    return static_cast<size_t>(fnv1a::fnv1a_64(pair.theory, hash));
  }
};/* struct NodeTheoryPairHashFunction */


/* Forward declarations */
namespace theory {
  class TheoryModel;
  class TheoryEngineModelBuilder;
  class ITEUtilities;

  namespace eq {
    class EqualityEngine;
  }/* CVC4::theory::eq namespace */

  namespace quantifiers {
    class TermDb;
  }

  class EntailmentCheckParameters;
  class EntailmentCheckSideEffects;
}/* CVC4::theory namespace */

class DecisionEngine;
class RemoveTermFormulas;
class UnconstrainedSimplifier;

/**
 * This is essentially an abstraction for a collection of theories.  A
 * TheoryEngine provides services to a PropEngine, making various
 * T-solvers look like a single unit to the propositional part of
 * CVC4.
 */
class TheoryEngine {

  /** Shared terms database can use the internals notify the theories */
  friend class SharedTermsDatabase;
  friend class theory::quantifiers::TermDb;

  /** Associated PropEngine engine */
  prop::PropEngine* d_propEngine;

  /** Access to decision engine */
  DecisionEngine* d_decisionEngine;

  /** Our context */
  context::Context* d_context;

  /** Our user context */
  context::UserContext* d_userContext;

  /**
   * A table of from theory IDs to theory pointers. Never use this table
   * directly, use theoryOf() instead.
   */
  theory::Theory* d_theoryTable[theory::THEORY_LAST];

  /**
   * A collection of theories that are "active" for the current run.
   * This set is provided by the user (as a logic string, say, in SMT-LIBv2
   * format input), or else by default it's all-inclusive.  This is important
   * because we can optimize for single-theory runs (no sharing), can reduce
   * the cost of walking the DAG on registration, etc.
   */
  const LogicInfo& d_logicInfo;

  /**
   * The database of shared terms.
   */
  SharedTermsDatabase d_sharedTerms;

  /**
   * Master equality engine, to share with theories.
   */
  theory::eq::EqualityEngine* d_masterEqualityEngine;

  /** notify class for master equality engine */
  class NotifyClass : public theory::eq::EqualityEngineNotify {
    TheoryEngine& d_te;
  public:
    NotifyClass(TheoryEngine& te): d_te(te) {}
    bool eqNotifyTriggerEquality(TNode equality, bool value) { return true; }
    bool eqNotifyTriggerPredicate(TNode predicate, bool value) { return true; }
    bool eqNotifyTriggerTermEquality(theory::TheoryId tag, TNode t1, TNode t2, bool value) { return true; }
    void eqNotifyConstantTermMerge(TNode t1, TNode t2) {}
    void eqNotifyNewClass(TNode t) { d_te.eqNotifyNewClass(t); }
    void eqNotifyPreMerge(TNode t1, TNode t2) { d_te.eqNotifyPreMerge(t1, t2); }
    void eqNotifyPostMerge(TNode t1, TNode t2) { d_te.eqNotifyPostMerge(t1, t2); }
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) { d_te.eqNotifyDisequal(t1, t2, reason); }
  };/* class TheoryEngine::NotifyClass */
  NotifyClass d_masterEENotify;

  /**
   * notification methods
   */
  void eqNotifyNewClass(TNode t);
  void eqNotifyPreMerge(TNode t1, TNode t2);
  void eqNotifyPostMerge(TNode t1, TNode t2);
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);

  /**
   * The quantifiers engine
   */
  theory::QuantifiersEngine* d_quantEngine;

  /**
   * Default model object
   */
  theory::TheoryModel* d_curr_model;
  bool d_aloc_curr_model;
  /**
   * Model builder object
   */
  theory::TheoryEngineModelBuilder* d_curr_model_builder;
  bool d_aloc_curr_model_builder;

  typedef std::unordered_map<Node, Node, NodeHashFunction> NodeMap;
  typedef std::unordered_map<TNode, Node, TNodeHashFunction> TNodeMap;

  /**
  * Cache for theory-preprocessing of assertions
   */
  NodeMap d_ppCache;

  /**
   * Used for "missed-t-propagations" dumping mode only.  A set of all
   * theory-propagable literals.
   */
  context::CDList<TNode> d_possiblePropagations;

  /**
   * Used for "missed-t-propagations" dumping mode only.  A
   * context-dependent set of those theory-propagable literals that
   * have been propagated.
   */
  context::CDHashSet<Node, NodeHashFunction> d_hasPropagated;


  /**
   * Statistics for a particular theory.
   */
  class Statistics {

    static std::string mkName(std::string prefix,
                              theory::TheoryId theory,
                              std::string suffix) {
      std::stringstream ss;
      ss << prefix << theory << suffix;
      return ss.str();
    }

  public:

    IntStat conflicts, propagations, lemmas, requirePhase, flipDecision, restartDemands;

    Statistics(theory::TheoryId theory);
    ~Statistics();
  };/* class TheoryEngine::Statistics */

  /**
   * An output channel for Theory that passes messages
   * back to a TheoryEngine.
   */
  class EngineOutputChannel : public theory::OutputChannel {
    friend class TheoryEngine;

    /**
     * The theory engine we're communicating with.
     */
    TheoryEngine* d_engine;

    /**
     * The statistics of the theory interractions.
     */
    Statistics d_statistics;

    /** The theory owning this channel. */
    theory::TheoryId d_theory;

   public:
    EngineOutputChannel(TheoryEngine* engine, theory::TheoryId theory)
        : d_engine(engine), d_statistics(theory), d_theory(theory) {}

    void safePoint(uint64_t amount) override {
      spendResource(amount);
      if (d_engine->d_interrupted) {
        throw theory::Interrupted();
      }
    }

    void conflict(TNode conflictNode,
                  std::unique_ptr<Proof> pf = nullptr) override;
    bool propagate(TNode literal) override;

    theory::LemmaStatus lemma(TNode lemma, ProofRule rule,
                              bool removable = false, bool preprocess = false,
                              bool sendAtoms = false) override;

    theory::LemmaStatus splitLemma(TNode lemma,
                                   bool removable = false) override;

    void demandRestart() override {
      NodeManager* curr = NodeManager::currentNM();
      Node restartVar = curr->mkSkolem(
          "restartVar", curr->booleanType(),
          "A boolean variable asserted to be true to force a restart");
      Trace("theory::restart")
          << "EngineOutputChannel<" << d_theory << ">::restart(" << restartVar
          << ")" << std::endl;
      ++d_statistics.restartDemands;
      lemma(restartVar, RULE_INVALID, true);
    }

    void requirePhase(TNode n, bool phase) override {
      Debug("theory") << "EngineOutputChannel::requirePhase(" << n << ", "
                      << phase << ")" << std::endl;
      ++d_statistics.requirePhase;
      d_engine->d_propEngine->requirePhase(n, phase);
    }

    bool flipDecision() override {
      Debug("theory") << "EngineOutputChannel::flipDecision()" << std::endl;
      ++d_statistics.flipDecision;
      return d_engine->d_propEngine->flipDecision();
    }

    void setIncomplete() override {
      Trace("theory") << "TheoryEngine::setIncomplete()" << std::endl;
      d_engine->setIncomplete(d_theory);
    }

    void spendResource(unsigned amount) override {
      d_engine->spendResource(amount);
    }

    void handleUserAttribute(const char* attr, theory::Theory* t) override {
      d_engine->handleUserAttribute(attr, t);
    }

   private:
    /**
     * A helper function for registering lemma recipes with the proof engine
     */
    void registerLemmaRecipe(Node lemma, Node originalLemma, bool preprocess,
                             theory::TheoryId theoryId);
  }; /* class TheoryEngine::EngineOutputChannel */

  /**
   * Output channels for individual theories.
   */
  EngineOutputChannel* d_theoryOut[theory::THEORY_LAST];

  /**
   * Are we in conflict.
   */
  context::CDO<bool> d_inConflict;

  /**
   * Called by the theories to notify of a conflict.
   */
  void conflict(TNode conflict, theory::TheoryId theoryId);

  /**
   * Debugging flag to ensure that shutdown() is called before the
   * destructor.
   */
  bool d_hasShutDown;

  /**
   * True if a theory has notified us of incompleteness (at this
   * context level or below).
   */
  context::CDO<bool> d_incomplete;

  /**
   * Called by the theories to notify that the current branch is incomplete.
   */
  void setIncomplete(theory::TheoryId theory) {
    d_incomplete = true;
  }


  /**
   * Mapping of propagations from recievers to senders.
   */
  typedef context::CDHashMap<NodeTheoryPair, NodeTheoryPair, NodeTheoryPairHashFunction> PropagationMap;
  PropagationMap d_propagationMap;

  /**
   * Timestamp of propagations
   */
  context::CDO<size_t> d_propagationMapTimestamp;

  /**
   * Literals that are propagated by the theory. Note that these are TNodes.
   * The theory can only propagate nodes that have an assigned literal in the
   * SAT solver and are hence referenced in the SAT solver.
   */
  context::CDList<TNode> d_propagatedLiterals;

  /**
   * The index of the next literal to be propagated by a theory.
   */
  context::CDO<unsigned> d_propagatedLiteralsIndex;

  /**
   * Called by the output channel to propagate literals and facts
   * @return false if immediate conflict
   */
  bool propagate(TNode literal, theory::TheoryId theory);

  /**
   * Internal method to call the propagation routines and collect the
   * propagated literals.
   */
  void propagate(theory::Theory::Effort effort);

  /**
   * Called by the output channel to request decisions "as soon as
   * possible."
   */
  void propagateAsDecision(TNode literal, theory::TheoryId theory);

  /**
   * A variable to mark if we added any lemmas.
   */
  bool d_lemmasAdded;

  /**
   * A variable to mark if the OutputChannel was "used" by any theory
   * since the start of the last check.  If it has been, we require
   * a FULL_EFFORT check before exiting and reporting SAT.
   *
   * See the documentation for the needCheck() function, below.
   */
  bool d_outputChannelUsed;

  /** Atom requests from lemmas */
  AtomRequests d_atomRequests;

  /**
   * Adds a new lemma, returning its status.
   * @param node the lemma
   * @param negated should the lemma be asserted negated
   * @param removable can the lemma be remove (restrictions apply)
   * @param needAtoms if not THEORY_LAST, then
   */
  theory::LemmaStatus lemma(TNode node,
                            ProofRule rule,
                            bool negated,
                            bool removable,
                            bool preprocess,
                            theory::TheoryId atomsTo);

  /** Enusre that the given atoms are send to the given theory */
  void ensureLemmaAtoms(const std::vector<TNode>& atoms, theory::TheoryId theory);

  RemoveTermFormulas& d_tform_remover;

  /** sort inference module */
  SortInference d_sortInfer;

  /** Time spent in theory combination */
  TimerStat d_combineTheoriesTime;

  Node d_true;
  Node d_false;

  /** Whether we were just interrupted (or not) */
  bool d_interrupted;
  ResourceManager* d_resourceManager;

  /** Container for lemma input and output channels. */
  LemmaChannels* d_channels;

public:

  /** Constructs a theory engine */
  TheoryEngine(context::Context* context, context::UserContext* userContext,
               RemoveTermFormulas& iteRemover, const LogicInfo& logic,
               LemmaChannels* channels);

  /** Destroys a theory engine */
  ~TheoryEngine();

  void interrupt();

  /** "Spend" a resource during a search or preprocessing.*/
  void spendResource(unsigned amount);

  /**
   * Adds a theory. Only one theory per TheoryId can be present, so if
   * there is another theory it will be deleted.
   */
  template <class TheoryClass>
  inline void addTheory(theory::TheoryId theoryId) {
    Assert(d_theoryTable[theoryId] == NULL && d_theoryOut[theoryId] == NULL);
    d_theoryOut[theoryId] = new EngineOutputChannel(this, theoryId);
    d_theoryTable[theoryId] =
        new TheoryClass(d_context, d_userContext, *d_theoryOut[theoryId],
                        theory::Valuation(this), d_logicInfo);
  }

  inline void setPropEngine(prop::PropEngine* propEngine) {
    Assert(d_propEngine == NULL);
    d_propEngine = propEngine;
  }

  inline void setDecisionEngine(DecisionEngine* decisionEngine) {
    Assert(d_decisionEngine == NULL);
    d_decisionEngine = decisionEngine;
  }

  /** Called when all initialization of options/logic is done */
  void finishInit();

  /**
   * Get a pointer to the underlying propositional engine.
   */
  inline prop::PropEngine* getPropEngine() const {
    return d_propEngine;
  }

  /**
   * Get a pointer to the underlying sat context.
   */
  inline context::Context* getSatContext() const {
    return d_context;
  }

  /**
   * Get a pointer to the underlying user context.
   */
  inline context::Context* getUserContext() const {
    return d_userContext;
  }

  /**
   * Get a pointer to the underlying quantifiers engine.
   */
  theory::QuantifiersEngine* getQuantifiersEngine() const {
    return d_quantEngine;
  }

private:

  /**
   * Helper for preprocess
   */
  Node ppTheoryRewrite(TNode term);

  /**
   * Queue of nodes for pre-registration.
   */
  std::queue<TNode> d_preregisterQueue;

  /**
   * Boolean flag denoting we are in pre-registration.
   */
  bool d_inPreregister;

  /**
   * Did the theories get any new facts since the last time we called
   * check()
   */
  context::CDO<bool> d_factsAsserted;

  /**
   * Map from equality atoms to theories that would like to be notified about them.
   */


  /**
   * Assert the formula to the given theory.
   * @param assertion the assertion to send (not necesserily normalized)
   * @param original the assertion as it was sent in from the propagating theory
   * @param toTheoryId the theory to assert to
   * @param fromTheoryId the theory that sent it
   */
  void assertToTheory(TNode assertion, TNode originalAssertion, theory::TheoryId toTheoryId, theory::TheoryId fromTheoryId);

  /**
   * Marks a theory propagation from a theory to a theory where a
   * theory could be the THEORY_SAT_SOLVER for literals coming from
   * or being propagated to the SAT solver. If the receiving theory
   * already recieved the literal, the method returns false, otherwise
   * it returns true.
   *
   * @param assertion the normalized assertion being sent
   * @param originalAssertion the actual assertion that was sent
   * @param toTheoryId the theory that is on the receiving end
   * @param fromTheoryId the theory that sent the assertino
   * @return true if a new assertion, false if theory already got it
   */
  bool markPropagation(TNode assertion, TNode originalAssertions, theory::TheoryId toTheoryId, theory::TheoryId fromTheoryId);

  /**
   * Computes the explanation by travarsing the propagation graph and
   * asking relevant theories to explain the propagations. Initially
   * the explanation vector should contain only the element (node, theory)
   * where the node is the one to be explained, and the theory is the
   * theory that sent the literal. The lemmaProofRecipe will contain a list
   * of the explanation steps required to produce the original node.
   */
  void getExplanation(std::vector<NodeTheoryPair>& explanationVector, LemmaProofRecipe* lemmaProofRecipe);

public:

  /**
   * Signal the start of a new round of assertion preprocessing
   */
  void preprocessStart();

  /**
   * Runs theory specific preprocessing on the non-Boolean parts of
   * the formula.  This is only called on input assertions, after ITEs
   * have been removed.
   */
  Node preprocess(TNode node);

  /** Notify (preprocessed) assertions. */
  void notifyPreprocessedAssertions(const std::vector<Node>& assertions);

  /** Return whether or not we are incomplete (in the current context). */
  inline bool isIncomplete() const { return d_incomplete; }

  /**
   * Returns true if we need another round of checking.  If this
   * returns true, check(FULL_EFFORT) _must_ be called by the
   * propositional layer before reporting SAT.
   *
   * This is especially necessary for incomplete theories that lazily
   * output some lemmas on FULL_EFFORT check (e.g. quantifier reasoning
   * outputing quantifier instantiations).  In such a case, a lemma can
   * be asserted that is simplified away (perhaps it's already true).
   * However, we must maintain the invariant that, if a theory uses the
   * OutputChannel, it implicitly requests that another check(FULL_EFFORT)
   * be performed before exit, even if no new facts are on its fact queue,
   * as it might decide to further instantiate some lemmas, precluding
   * a SAT response.
   */
  inline bool needCheck() const {
    return d_outputChannelUsed || d_lemmasAdded;
  }

  /**
   * This is called at shutdown time by the SmtEngine, just before
   * destruction.  It is important because there are destruction
   * ordering issues between PropEngine and Theory.
   */
  void shutdown();

  /**
   * Solve the given literal with a theory that owns it.
   */
  theory::Theory::PPAssertStatus solve(TNode literal,
                                    theory::SubstitutionMap& substitutionOut);

  /**
   * Preregister a Theory atom with the responsible theory (or
   * theories).
   */
  void preRegister(TNode preprocessed);

  /**
   * Assert the formula to the appropriate theory.
   * @param node the assertion
   */
  void assertFact(TNode node);

  /**
   * Check all (currently-active) theories for conflicts.
   * @param effort the effort level to use
   */
  void check(theory::Theory::Effort effort);

  /**
   * Run the combination framework.
   */
  void combineTheories();

  /**
   * Calls ppStaticLearn() on all theories, accumulating their
   * combined contributions in the "learned" builder.
   */
  void ppStaticLearn(TNode in, NodeBuilder<>& learned);

  /**
   * Calls presolve() on all theories and returns true
   * if one of the theories discovers a conflict.
   */
  bool presolve();

   /**
   * Calls postsolve() on all theories.
   */
  void postsolve();

  /**
   * Calls notifyRestart() on all active theories.
   */
  void notifyRestart();

  void getPropagatedLiterals(std::vector<TNode>& literals) {
    for (; d_propagatedLiteralsIndex < d_propagatedLiterals.size(); d_propagatedLiteralsIndex = d_propagatedLiteralsIndex + 1) {
      Debug("getPropagatedLiterals") << "TheoryEngine::getPropagatedLiterals: propagating: " << d_propagatedLiterals[d_propagatedLiteralsIndex] << std::endl;
      literals.push_back(d_propagatedLiterals[d_propagatedLiteralsIndex]);
    }
  }

  Node getNextDecisionRequest();

  bool properConflict(TNode conflict) const;
  bool properPropagation(TNode lit) const;
  bool properExplanation(TNode node, TNode expl) const;

  /**
   * Returns an explanation of the node propagated to the SAT solver.
   */
  Node getExplanation(TNode node);

  /**
   * Returns an explanation of the node propagated to the SAT solver and the theory
   * that propagated it.
   */
  Node getExplanationAndRecipe(TNode node, LemmaProofRecipe* proofRecipe);

  /**
   * collect model info
   */
  bool collectModelInfo(theory::TheoryModel* m);
  /** post process model */
  void postProcessModel( theory::TheoryModel* m );

  /**
   * Get the current model
   */
  theory::TheoryModel* getModel();

  /** get synth solutions
   *
   * This function adds entries to sol_map that map functions-to-synthesize with
   * their solutions, for all active conjectures. This should be called
   * immediately after the solver answers unsat for sygus input.
   *
   * For details on what is added to sol_map, see
   * CegConjecture::getSynthSolutions.
   */
  void getSynthSolutions(std::map<Node, Node>& sol_map);

  /**
   * Get the model builder
   */
  theory::TheoryEngineModelBuilder* getModelBuilder() { return d_curr_model_builder; }

  /**
   * Get the theory associated to a given Node.
   *
   * @returns the theory, or NULL if the TNode is
   * of built-in type.
   */
  inline theory::Theory* theoryOf(TNode node) const {
    return d_theoryTable[theory::Theory::theoryOf(node)];
  }

  /**
   * Get the theory associated to a the given theory id.
   *
   * @returns the theory
   */
  inline theory::Theory* theoryOf(theory::TheoryId theoryId) const {
    return d_theoryTable[theoryId];
  }

  inline bool isTheoryEnabled(theory::TheoryId theoryId) const {
    return d_logicInfo.isTheoryEnabled(theoryId);
  }

  /**
   * Returns the equality status of the two terms, from the theory
   * that owns the domain type.  The types of a and b must be the same.
   */
  theory::EqualityStatus getEqualityStatus(TNode a, TNode b);

  /**
   * Returns the value that a theory that owns the type of var currently
   * has (or null if none);
   */
  Node getModelValue(TNode var);

  /**
   * Takes a literal and returns an equivalent literal that is guaranteed to be a SAT literal
   */
  Node ensureLiteral(TNode n);

  /**
   * Print all instantiations made by the quantifiers module.
   */
  void printInstantiations( std::ostream& out );

  /**
   * Print solution for synthesis conjectures found by ce_guided_instantiation module
   */
  void printSynthSolution( std::ostream& out );

  /**
   * Get list of quantified formulas that were instantiated
   */
  void getInstantiatedQuantifiedFormulas( std::vector< Node >& qs );

  /**
   * Get instantiation methods
   *   first inputs forall x.q[x] and returns ( q[a], ..., q[z] )
   *   second inputs forall x.q[x] and returns ( a, ..., z ) 
   *   third and fourth return mappings e.g. forall x.q1[x] -> ( q1[a]...q1[z] ) , ... , forall x.qn[x] -> ( qn[a]...qn[z] )
   */
  void getInstantiations( Node q, std::vector< Node >& insts );
  void getInstantiationTermVectors( Node q, std::vector< std::vector< Node > >& tvecs );
  void getInstantiations( std::map< Node, std::vector< Node > >& insts );
  void getInstantiationTermVectors( std::map< Node, std::vector< std::vector< Node > > >& insts );
  
  /**
   * Get instantiated conjunction, returns q[t1] ^ ... ^ q[tn] where t1...tn are current set of instantiations for q.
   *   Can be used for quantifier elimination when satisfiable and q[t1] ^ ... ^ q[tn] |= q
   */
  Node getInstantiatedConjunction( Node q );

  /**
   * Forwards an entailment check according to the given theoryOfMode.
   * See theory.h for documentation on entailmentCheck().
   */
  std::pair<bool, Node> entailmentCheck(theory::TheoryOfMode mode, TNode lit, const theory::EntailmentCheckParameters* params = NULL, theory::EntailmentCheckSideEffects* out = NULL);

private:

  /** Default visitor for pre-registration */
  PreRegisterVisitor d_preRegistrationVisitor;

  /** Visitor for collecting shared terms */
  SharedTermsVisitor d_sharedTermsVisitor;

  /** Dump the assertions to the dump */
  void dumpAssertions(const char* tag);

  /**
   * A collection of ite preprocessing passes.
   */
  theory::ITEUtilities* d_iteUtilities;


  /** For preprocessing pass simplifying unconstrained expressions */
  UnconstrainedSimplifier* d_unconstrainedSimp;

  /** For preprocessing pass lifting bit-vectors of size 1 to booleans */
  theory::bv::BvToBoolPreprocessor d_bvToBoolPreprocessor;
public:
  void staticInitializeBVOptions(const std::vector<Node>& assertions);
  void ppBvToBool(const std::vector<Node>& assertions, std::vector<Node>& new_assertions);
  void ppBoolToBv(const std::vector<Node>& assertions, std::vector<Node>& new_assertions);
  bool ppBvAbstraction(const std::vector<Node>& assertions, std::vector<Node>& new_assertions);
  void mkAckermanizationAssertions(std::vector<Node>& assertions);

  Node ppSimpITE(TNode assertion);
  /** Returns false if an assertion simplified to false. */
  bool donePPSimpITE(std::vector<Node>& assertions);

  void ppUnconstrainedSimp(std::vector<Node>& assertions);

  SharedTermsDatabase* getSharedTermsDatabase() { return &d_sharedTerms; }

  theory::eq::EqualityEngine* getMasterEqualityEngine() { return d_masterEqualityEngine; }

  RemoveTermFormulas* getTermFormulaRemover() { return &d_tform_remover; }

  SortInference* getSortInference() { return &d_sortInfer; }

  /** Prints the assertions to the debug stream */
  void printAssertions(const char* tag);

  /** Theory alternative is in use. */
  bool useTheoryAlternative(const std::string& name);

  /** Enables using a theory alternative by name. */
  void enableTheoryAlternative(const std::string& name);

private:
  std::set< std::string > d_theoryAlternatives;

  std::map< std::string, std::vector< theory::Theory* > > d_attr_handle;

 public:
  /** Set user attribute.
   * 
   * This function is called when an attribute is set by a user.  In SMT-LIBv2
   * this is done via the syntax (! n :attr)
   */
  void setUserAttribute(const std::string& attr,
                        Node n,
                        const std::vector<Node>& node_values,
                        const std::string& str_value);

  /** Handle user attribute.
   * 
   * Associates theory t with the attribute attr.  Theory t will be
   * notified whenever an attribute of name attr is set.
   */
  void handleUserAttribute(const char* attr, theory::Theory* t);

  /**
   * Check that the theory assertions are satisfied in the model.
   * This function is called from the smt engine's checkModel routine.
   */
  void checkTheoryAssertionsWithModel(bool hardFailure);

 private:
  IntStat d_arithSubstitutionsAdded;

};/* class TheoryEngine */

}/* CVC4 namespace */

#endif /* __CVC4__THEORY_ENGINE_H */
