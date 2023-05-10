/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An inference manager for Theory.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__THEORY_INFERENCE_MANAGER_H
#define CVC5__THEORY__THEORY_INFERENCE_MANAGER_H

#include <memory>

#include "context/cdhashset.h"
#include "expr/node.h"
#include "proof/proof_rule.h"
#include "proof/trust_node.h"
#include "smt/env_obj.h"
#include "theory/inference_id.h"
#include "theory/output_channel.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {

class ProofNodeManager;
class AnnotationProofGenerator;
class EagerProofGenerator;

namespace theory {

class Theory;
class TheoryState;
class DecisionManager;
class InferenceIdProofAnnotator;
namespace eq {
class EqualityEngine;
class ProofEqEngine;
}

/**
 * The base class for inference manager. An inference manager is a wrapper
 * around the output channel and the official equality engine of a Theory.
 * It is used for ensuring that the equality engine and output channel
 * are used properly. This includes the following invariants:
 *
 * (1) The state tracks conflicts.
 * In particular, TheoryState::isInConflict returns true whenever we have
 * called OutputChannel::conflict in the current context, which we enforce
 * by always setting d_state.notifyInConflict at the same time we send
 * conflicts on the output channel.
 *
 * (2) The theory is notified of (internal) facts.
 * In particular, Theory::preNotifyFact and Theory::notifyFact are called
 * (with isInternal = true) whenever we assert internal facts using
 * assertFactInernal below, mirroring what is done for facts from the fact
 * queue (where isInternal = false).
 *
 * (3) The proof equality engine is used whenever proofs are enabled (when
 * the proof node manager provided to this class is non-null). Notice this
 * class automatically will construct a proof equality engine during
 * setEqualityEngine, and use it for handling variants of assertInternalFact
 * below that involve proofs.
 */
class TheoryInferenceManager : protected EnvObj
{
  typedef context::CDHashSet<Node> NodeSet;

 public:
  /**
   * Constructor, note that state should be the official state of theory t.
   *
   * @param t The theory this inference manager is for
   * @param state The state of the theory
   * @param pnm The proof node manager, which if non-null, enables proofs for
   * this inference manager
   * @param statsName The name of the inference manager, which is used for
   * giving unique names for statistics,
   * @param cacheLemmas Whether all lemmas sent using this theory inference
   * manager are added to a user-context dependent cache. This means that
   * only lemmas that are unique after rewriting are sent to the theory engine
   * from this inference manager.
   */
  TheoryInferenceManager(Env& env,
                         Theory& t,
                         TheoryState& state,
                         const std::string& statsName,
                         bool cacheLemmas = true);
  virtual ~TheoryInferenceManager();
  //--------------------------------------- initialization
  /**
   * Set equality engine, ee is a pointer to the official equality engine
   * of theory.
   */
  void setEqualityEngine(eq::EqualityEngine* ee);
  /** Set the decision manager */
  void setDecisionManager(DecisionManager* dm);
  //--------------------------------------- end initialization
  /**
   * Are proofs enabled in this inference manager? Returns true if the proof
   * node manager pnm provided to the constructor of this class was non-null.
   */
  bool isProofEnabled() const;
  /** Get the underlying proof equality engine */
  eq::ProofEqEngine* getProofEqEngine();
  /**
   * Reset, which resets counters regarding the number of added lemmas and
   * internal facts. This method should be manually called by the theory at
   * the appropriate time for the purpose of tracking the usage of this
   * inference manager.
   *
   * For example, some theories implement an internal checking loop that
   * repeats while new facts are added. The theory should call reset at the
   * beginning of this loop and repeat its strategy while hasAddedFact is true.
   */
  void reset();
  /**
   * Returns true if we are in conflict, or if we have sent a lemma or fact
   * since the last call to reset.
   */
  bool hasSent() const;
  //--------------------------------------- propagations
  /**
   * T-propagate literal lit, possibly encountered by equality engine,
   * returns false if we are in conflict.
   *
   * Note that this is the preferred method to call on
   * EqualityEngineNotify::eqNotifyTriggerPredicate and
   * EqualityEngineNotify::eqNotifyTriggerTermEquality.
   */
  virtual bool propagateLit(TNode lit);
  /**
   * Return an explanation for the literal represented by parameter lit
   * (which was previously propagated by this theory). By default, this
   * returns the explanation given by the official equality engine of the
   * Theory, if it exists.
   */
  virtual TrustNode explainLit(TNode lit);
  //--------------------------------------- conflicts
  /**
   * Raise conflict, called when constants a and b merge. Sends the conflict
   * on the output channel corresponding to the equality engine's explanation
   * of (= a b). The proof equality engine (if it exists) will be used as the
   * proof generator.
   *
   * Note that this is the preferred method to call on
   * EqualityEngineNotify::eqNotifyConstantTermMerge.
   */
  void conflictEqConstantMerge(TNode a, TNode b);
  /**
   * Raise conflict conf (of any form), without proofs. This method should
   * only be called if there is not yet proof support in the given theory.
   */
  void conflict(TNode conf, InferenceId id);
  /**
   * Raise trusted conflict tconf (of any form) where a proof generator has
   * been provided (as part of the trust node) in a custom way.
   */
  void trustedConflict(TrustNode tconf, InferenceId id);
  /**
   * Explain and send conflict from contradictory facts. This method is called
   * when the proof rule id with premises exp and arguments args concludes
   * false. This method sends a trusted conflict corresponding to the official
   * equality engine's explanation of literals in exp, with the proof equality
   * engine as the proof generator (if it exists).
   */
  void conflictExp(InferenceId id,
                   PfRule pfr,
                   const std::vector<Node>& exp,
                   const std::vector<Node>& args);
  /**
   * Make the trust node corresponding to the conflict of the above form. It is
   * the responsibility of the caller to subsequently call trustedConflict with
   * the returned trust node.
   */
  TrustNode mkConflictExp(PfRule pfr,
                          const std::vector<Node>& exp,
                          const std::vector<Node>& args);
  /**
   * Explain and send conflict from contradictory facts. This method is called
   * when proof generator pg has a proof of false from free assumptions exp.
   * This method sends a trusted conflict corresponding to the official
   * equality engine's explanation of literals in exp, with the proof equality
   * engine as the proof generator (if it exists), where pg provides the
   * final step(s) of this proof during this call.
   */
  void conflictExp(InferenceId id,
                   const std::vector<Node>& exp,
                   ProofGenerator* pg);
  /**
   * Make the trust node corresponding to the conflict of the above form. It is
   * the responsibility of the caller to subsequently call trustedConflict with
   * the returned trust node.
   */
  TrustNode mkConflictExp(const std::vector<Node>& exp, ProofGenerator* pg);
  //--------------------------------------- lemmas
  /**
   * Send (trusted) lemma lem with property p on the output channel.
   *
   * @param tlem The trust node containing the lemma and its proof generator.
   * @param p The property of the lemma
   * @return true if the lemma was sent on the output channel.
   */
  bool trustedLemma(const TrustNode& tlem,
                    InferenceId id,
                    LemmaProperty p = LemmaProperty::NONE);
  /**
   * Send lemma lem with property p on the output channel. Same as above, with
   * a node instead of a trust node.
   */
  bool lemma(TNode lem, InferenceId id, LemmaProperty p = LemmaProperty::NONE);
  /**
   * Explained lemma. This should be called when
   *   ( exp => conc )
   * is a valid theory lemma. This method adds a lemma where part of exp
   * is replaced by its explanation according to the official equality engine
   * of the theory.
   *
   * In particular, this method adds a lemma on the output channel of the form
   *   ( ^_{e in exp \ noExplain} EXPLAIN(e) ^ noExplain ) => conc
   * where EXPLAIN(e) returns the explanation of literal e according to the
   * official equality engine of the theory. Note that noExplain is the *subset*
   * of exp that should not be explained.
   *
   * @param conc The conclusion of the lemma
   * @param id The proof rule concluding conc
   * @param exp The set of (all) literals that imply conc
   * @param noExplain The subset of exp that should not be explained by the
   * equality engine
   * @param args The arguments to the proof step concluding conc
   * @param p The property of the lemma
   * @return true if the lemma was sent on the output channel.
   */
  bool lemmaExp(Node conc,
                InferenceId id,
                PfRule pfr,
                const std::vector<Node>& exp,
                const std::vector<Node>& noExplain,
                const std::vector<Node>& args,
                LemmaProperty p = LemmaProperty::NONE);
  /**
   * Make the trust node for the above method. It is responsibility of the
   * caller to subsequently call trustedLemma with the returned trust node.
   */
  TrustNode mkLemmaExp(Node conc,
                       PfRule id,
                       const std::vector<Node>& exp,
                       const std::vector<Node>& noExplain,
                       const std::vector<Node>& args);
  /**
   * Same as above, but where pg can provide a proof of conc from free
   * assumptions in exp. This sends a trusted lemma on the output channel where
   * the proof equality engine is the proof generator. The generator pg
   * is asked to provide the final step(s) of this proof during this call.
   *
   * @param conc The conclusion of the lemma
   * @param exp The set of (all) literals that imply conc
   * @param noExplain The subset of exp that should not be explained by the
   * equality engine
   * @param pg If non-null, the proof generator who can provide a proof of conc.
   * @param p The property of the lemma
   * @return true if the lemma was sent on the output channel.
   */
  bool lemmaExp(Node conc,
                InferenceId id,
                const std::vector<Node>& exp,
                const std::vector<Node>& noExplain,
                ProofGenerator* pg = nullptr,
                LemmaProperty p = LemmaProperty::NONE);
  /**
   * Make the trust node for the above method. It is responsibility of the
   * caller to subsequently call trustedLemma with the returned trust node.
   */
  TrustNode mkLemmaExp(Node conc,
                       const std::vector<Node>& exp,
                       const std::vector<Node>& noExplain,
                       ProofGenerator* pg = nullptr);
  /**
   * Has this inference manager cached and sent the given lemma (in this user
   * context)? This method can be overridden by the particular manager. If not,
   * this returns true if lem is in the cache d_lemmasSent maintained by this
   * class. Notice that the default cache in this base class is not dependent
   * on the lemma property.
   */
  virtual bool hasCachedLemma(TNode lem, LemmaProperty p);
  /** The number of lemmas we have sent since the last call to reset */
  uint32_t numSentLemmas() const;
  /** Have we added a lemma since the last call to reset? */
  bool hasSentLemma() const;
  //--------------------------------------- internal facts
  /**
   * Assert internal fact. This is recommended method for asserting "internal"
   * facts into the equality engine of the theory. In particular, this method
   * should be used for anything the theory infers that is not sent on the
   * output channel as a propagation or lemma. This method ensures that the
   * Theory's preNotifyFact and notifyFact method have been called with
   * isInternal = true.
   *
   * Note this method should never be used when proofs are enabled.
   *
   * @param atom The atom of the fact to assert
   * @param pol Its polarity
   * @param exp Its explanation, i.e. ( exp => (~) atom ) is valid.
   * @return true if the fact was processed, i.e. it was asserted to the
   * equality engine or preNotifyFact returned true.
   */
  bool assertInternalFact(TNode atom, bool pol, InferenceId id, TNode exp);
  /**
   * Assert internal fact, with a proof step justification. Notice that if
   * proofs are not enabled in this inference manager, then this asserts
   * a fact to the equality engine in the normal way.
   *
   * @param atom The atom of the fact to assert
   * @param pol Its polarity
   * @param id The proof rule identifier of the proof step
   * @param exp Its explanation, interpreted as a conjunction
   * @param args The arguments of the proof step
   * @return true if the fact was processed, i.e. it was asserted to the
   * equality engine or preNotifyFact returned true.
   */
  bool assertInternalFact(TNode atom,
                          bool pol,
                          InferenceId id,
                          PfRule pfr,
                          const std::vector<Node>& exp,
                          const std::vector<Node>& args);
  /**
   * Assert internal fact, with a proof generator justification. Same as above,
   * but with a proof generator instead of an explicit step.
   *
   * @param atom The atom of the fact to assert
   * @param pol Its polarity
   * @param exp Its explanation, interpreted as a conjunction
   * @param pg The proof generator for this step. If non-null, pg must be able
   * to provide a proof concluding (~) atom from free asumptions in exp in
   * the remainder of the current SAT context.
   * @return true if the fact was processed, i.e. it was asserted to the
   * equality engine or preNotifyFact returned true.
   */
  bool assertInternalFact(TNode atom,
                          bool pol,
                          InferenceId id,
                          const std::vector<Node>& exp,
                          ProofGenerator* pg);
  /** The number of internal facts we have added since the last call to reset */
  uint32_t numSentFacts() const;
  /** Have we added a internal fact since the last call to reset? */
  bool hasSentFact() const;
  //--------------------------------------- phase requirements
  /** Get the decision manager, which manages decision strategies. */
  DecisionManager* getDecisionManager();
  /**
   * Set that literal n has SAT phase requirement pol, that is, it should be
   * decided with polarity pol, for details see OutputChannel::requirePhase.
   */
  void requirePhase(TNode n, bool pol);

  /**
   * Forward to OutputChannel::spendResource() to spend resources.
   */
  void spendResource(Resource r);

  /**
   * Forward to OutputChannel::safePoint() to spend resources.
   */
  void safePoint(Resource r);
  /**
   * Notification from a theory that it realizes it is model unsound at
   * this SAT context level. In other words, we cannot answer "sat" in this
   * SAT context.
   *
   * Note that we use SAT context for model unsoundness, since the typical use
   * case is that an asserted literal cannot be verified for the model under
   * construction, where asserted literals are SAT-context dependent.
   */
  void setModelUnsound(IncompleteId id);
  /**
   * Notification from a theory that it realizes it is refutation unsound at
   * this user context level. In other words, we cannot answer "unsat" in this
   * user context.
   *
   * Note that we use user context for refutation unsoundness, since typically
   * the source of refutation unsoundness is a lemma, which are user context
   * dependent.
   */
  void setRefutationUnsound(IncompleteId id);
  /**
   * Notify this inference manager that a conflict was sent in this SAT context.
   * This method is called via TheoryEngine when a conflict is sent.
   */
  virtual void notifyInConflict();

 protected:
  /**
   * Process internal fact. This is a common helper method for the
   * assertInternalFact variants above. Returns true if the fact was processed.
   */
  bool processInternalFact(TNode atom,
                           bool pol,
                           InferenceId iid,
                           PfRule id,
                           const std::vector<Node>& exp,
                           const std::vector<Node>& args,
                           ProofGenerator* pg);
  /**
   * Explain conflict from constants merging in the equality engine. This
   * method is called by conflictEqConstantMerge. By default, it returns
   * the explanation of the official equality engine of the theory, if it
   * exists.
   */
  virtual TrustNode explainConflictEqConstantMerge(TNode a, TNode b);
  /**
   * Explain formula n (which is possibly a conjunction with no nested
   * conjunctions), add its explanation to assumptions.
   */
  void explain(TNode n, std::vector<TNode>& assumptions);
  /**
   * Explain formula n (which is possibly a conjunction with no nested
   * conjunctions), return the explanation as a conjunction.
   */
  Node mkExplain(TNode n);
  /**
   * Explain the set of formulas in exp using the official equality engine of
   * the theory. We ask the equality engine to explain literals in exp
   * that do not occur in noExplain, and return unchanged those that occur in
   * noExplain. Note the vector noExplain should be a subset of exp.
   */
  Node mkExplainPartial(const std::vector<Node>& exp,
                        const std::vector<Node>& noExplain);
  /**
   * Cache that lemma lem is being sent with property p. Return true if it
   * did not already exist in the cache maintained by this class. If this
   * method is not overridden, then we use the d_lemmasSent cache maintained
   * by this class, which notice is not dependent on lemma property. If
   * the lemma property should be taken into account, the manager should
   * override this method to take the lemma property into account as needed.
   */
  virtual bool cacheLemma(TNode lem, LemmaProperty p);
  /**
   * Return the trust node that is equivalent to trn, but its proof (if asked
   * for) will be wrapped in (ANNOTATE ... :args id). We return a trust
   * node of trust node kind CONFLICT if isConflict is true.
   */
  TrustNode annotateId(const TrustNode& trn,
                       InferenceId id,
                       bool isConflict = false);
  /** The theory object */
  Theory& d_theory;
  /** Reference to the state of theory */
  TheoryState& d_theoryState;
  /** Reference to the output channel of the theory */
  OutputChannel& d_out;
  /** Pointer to equality engine of the theory. */
  eq::EqualityEngine* d_ee;
  /** Pointer to the decision manager */
  DecisionManager* d_decManager;
  /** A proof equality engine */
  eq::ProofEqEngine* d_pfee;
  /** The proof equality engine we allocated */
  std::unique_ptr<eq::ProofEqEngine> d_pfeeAlloc;
  /** Proof generator for trusted THEORY_LEMMA steps */
  std::unique_ptr<EagerProofGenerator> d_defaultPg;
  /** The inference id proof annotator */
  std::unique_ptr<InferenceIdProofAnnotator> d_iipa;
  /** The annotation proof generator */
  std::unique_ptr<AnnotationProofGenerator> d_apg;
  /** Whether this manager caches lemmas */
  bool d_cacheLemmas;
  /**
   * The keep set of this class. This set is maintained to ensure that
   * facts and their explanations are ref-counted. Since facts and their
   * explanations are SAT-context-dependent, this set is also
   * SAT-context-dependent.
   */
  NodeSet d_keep;
  /**
   * A cache of all lemmas sent, which is a user-context-dependent set of
   * nodes. Notice that this cache does not depedent on lemma property.
   */
  NodeSet d_lemmasSent;
  /** The number of conflicts sent since the last call to reset. */
  uint32_t d_numConflicts;
  /** The number of lemmas sent since the last call to reset. */
  uint32_t d_numCurrentLemmas;
  /** The number of internal facts added since the last call to reset. */
  uint32_t d_numCurrentFacts;
  /** Statistics for conflicts sent via this inference manager. */
  HistogramStat<InferenceId> d_conflictIdStats;
  /** Statistics for facts sent via this inference manager. */
  HistogramStat<InferenceId> d_factIdStats;
  /** Statistics for lemmas sent via this inference manager. */
  HistogramStat<InferenceId> d_lemmaIdStats;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__THEORY_INFERENCE_MANAGER_H */
