/*********************                                                        */
/*! \file theory_inference_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief An inference manager for Theory
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__THEORY_INFERENCE_MANAGER_H
#define CVC4__THEORY__THEORY_INFERENCE_MANAGER_H

#include <memory>

#include "context/cdhashset.h"
#include "expr/node.h"
#include "theory/output_channel.h"
#include "theory/theory_state.h"
#include "theory/trust_node.h"
#include "theory/uf/proof_equality_engine.h"

namespace CVC4 {

class ProofNodeManager;

namespace theory {

class Theory;
namespace eq {
class EqualityEngine;
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
class TheoryInferenceManager
{
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

 public:
  /**
   * Constructor, note that state should be the official state of theory t.
   */
  TheoryInferenceManager(Theory& t, TheoryState& state, ProofNodeManager* pnm);
  virtual ~TheoryInferenceManager() {}
  /**
   * Set equality engine, ee is a pointer to the official equality engine
   * of theory.
   */
  void setEqualityEngine(eq::EqualityEngine* ee);
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
  //--------------------------------------- propagations
  /**
   * T-propagate literal lit, possibly encountered by equality engine,
   * returns false if we are in conflict.
   *
   * Note that this is the preferred method to call on
   * EqualityEngineNotify::eqNotifyTriggerPredicate and
   * EqualityEngineNotify::eqNotifyTriggerTermEquality.
   */
  bool propagateLit(TNode lit);
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
  void conflict(TNode conf);
  /**
   * Raise trusted conflict tconf (of any form) where a proof generator has
   * been provided in a custom way.
   */
  void trustedConflict(TrustNode tconf);
  /**
   * Explain and send conflict from contradictory facts. This method is called
   * when the proof rule id with premises exp and arguments args concludes
   * false. This method sends a trusted conflict corresponding to the official
   * equality engine's explanation of literals in exp, with the proof equality
   * engine as the proof generator (if it exists).
   */
  void conflictExp(PfRule id,
                   const std::vector<Node>& exp,
                   const std::vector<Node>& args);
  //--------------------------------------- lemmas
  /**
   * Send (trusted) lemma lem with property p on the output channel.
   *
   * @param tlem The trust node containing the lemma and its proof generator.
   * @param p The property of the lemma
   * @param doCache If true, we send the lemma only if it has not already been
   * cached (see cacheLemma), and add it to the cache during this call.
   * @return true if the lemma was sent on the output channel.
   */
  bool trustedLemma(const TrustNode& tlem,
                    LemmaProperty p = LemmaProperty::NONE,
                    bool doCache = true);
  /**
   * Send lemma lem with property p on the output channel. Same as above, with
   * a node instead of a trust node.
   */
  bool lemma(TNode lem,
             LemmaProperty p = LemmaProperty::NONE,
             bool doCache = true);
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
   * @param doCache Whether to check and add the lemma to the cache
   * @return true if the lemma was sent on the output channel.
   */
  bool lemmaExp(Node conc,
                PfRule id,
                const std::vector<Node>& exp,
                const std::vector<Node>& noExplain,
                const std::vector<Node>& args,
                LemmaProperty p = LemmaProperty::NONE,
                bool doCache = true);
  /**
   * Same as above, but where pg can provide a proof of conc from free
   * assumptions in exp. It is required to do so in the remainder of the user
   * context when this method returns true.
   *
   * @param conc The conclusion of the lemma
   * @param exp The set of (all) literals that imply conc
   * @param noExplain The subset of exp that should not be explained by the
   * equality engine
   * @param pg If non-null, the proof generator who can provide a proof of conc.
   * @param p The property of the lemma
   * @param doCache Whether to check and add the lemma to the cache
   * @return true if the lemma was sent on the output channel.
   */
  bool lemmaExp(Node conc,
                const std::vector<Node>& exp,
                const std::vector<Node>& noExplain,
                ProofGenerator* pg = nullptr,
                LemmaProperty p = LemmaProperty::NONE,
                bool doCache = true);
  /**
   * Has this inference manager cached and sent the given lemma (in this user
   * context)? This method can be overridden by the particular manager. If not,
   * this returns true if lem is in the cache d_lemmasSent maintained by this
   * class. Notice that the default cache in this base class is not dependent
   * on the lemma property.
   */
  virtual bool hasCachedLemma(TNode lem, LemmaProperty p);
  /** The number of lemmas we have sent since the last call to reset */
  uint32_t numAddedLemmas() const;
  /** Have we added a lemma since the last call to reset? */
  bool hasAddedLemma() const;
  //--------------------------------------- internal facts
  /**
   * Assert internal fact. This is recommended method for asserting "internal"
   * facts into the equality engine of the theory. In particular, this method
   * should be used for anything the theory infers that is not sent on the
   * output channel as a propagation or lemma. This method ensures that the
   * Theory's preNotifyFact and notifyFact method have been called with
   * isInternal = true.
   *
   * @param atom The atom of the fact to assert
   * @param pol Its polarity
   * @param exp Its explanation, i.e. ( exp => (~) atom ) is valid.
   */
  void assertInternalFact(TNode atom, bool pol, TNode exp);
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
   */
  void assertInternalFact(TNode atom,
                          bool pol,
                          PfRule id,
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
   */
  void assertInternalFact(TNode atom,
                          bool pol,
                          const std::vector<Node>& exp,
                          ProofGenerator* pg);
  /** The number of internal facts we have added since the last call to reset */
  uint32_t numAddedFacts() const;
  /** Have we added a internal fact since the last call to reset? */
  bool hasAddedFact() const;

 protected:
  /**
   * Process internal fact. This is a common helper method for the
   * assertInternalFact variants above.
   */
  void processInternalFact(TNode atom,
                           bool pol,
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
  /** The theory object */
  Theory& d_theory;
  /** Reference to the state of theory */
  TheoryState& d_theoryState;
  /** Reference to the output channel of the theory */
  OutputChannel& d_out;
  /** Pointer to equality engine of the theory. */
  eq::EqualityEngine* d_ee;
  /** A proof equality engine */
  std::unique_ptr<eq::ProofEqEngine> d_pfee;
  /** The proof node manager of the theory */
  ProofNodeManager* d_pnm;
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
  /** The number of lemmas sent since the last call to reset. */
  uint32_t d_numCurrentLemmas;
  /** The number of internal facts added since the last call to reset. */
  uint32_t d_numCurrentFacts;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__THEORY_INFERENCE_MANAGER_H */
