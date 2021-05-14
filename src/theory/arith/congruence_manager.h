/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir, Tim King, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "cvc5_private.h"

#pragma once

#include "context/cdhashmap.h"
#include "context/cdlist.h"
#include "context/cdmaybe.h"
#include "context/cdtrail_queue.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/arithvar.h"
#include "theory/arith/callbacks.h"
#include "theory/arith/constraint_forward.h"
#include "theory/trust_node.h"
#include "theory/uf/equality_engine_notify.h"
#include "util/dense_map.h"
#include "util/statistics_stats.h"

namespace cvc5 {

class ProofNodeManager;

namespace context {
class Context;
class UserContext;
}

namespace theory {

class EagerProofGenerator;
struct EeSetupInfo;

namespace eq {
class ProofEqEngine;
class EqualityEngine;
}

namespace arith {

class ArithVariables;

class ArithCongruenceManager {
private:
  context::CDRaised d_inConflict;
  RaiseEqualityEngineConflict d_raiseConflict;

  /**
   * The set of ArithVars equivalent to a pair of terms.
   * If this is 0 or cannot be 0, this can be signalled.
   * The pair of terms for the congruence is stored in watched equalities.
   */
  DenseSet d_watchedVariables;
  /** d_watchedVariables |-> (= x y) */
  ArithVarToNodeMap d_watchedEqualities;


  class ArithCongruenceNotify : public eq::EqualityEngineNotify {
  private:
    ArithCongruenceManager& d_acm;
  public:
    ArithCongruenceNotify(ArithCongruenceManager& acm);

    bool eqNotifyTriggerPredicate(TNode predicate, bool value) override;

    bool eqNotifyTriggerTermEquality(TheoryId tag,
                                     TNode t1,
                                     TNode t2,
                                     bool value) override;

    void eqNotifyConstantTermMerge(TNode t1, TNode t2) override;
    void eqNotifyNewClass(TNode t) override;
    void eqNotifyMerge(TNode t1, TNode t2) override;
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override;
  };
  ArithCongruenceNotify d_notify;

  context::CDList<Node> d_keepAlive;

  /** Store the propagations. */
  context::CDTrailQueue<Node> d_propagatations;

  /* This maps the node a theory engine will request on an explain call to
   * to its corresponding PropUnit.
   * This is node is potentially both the propagation or
   * Rewriter::rewrite(propagation).
   */
  typedef context::CDHashMap<Node, size_t> ExplainMap;
  ExplainMap d_explanationMap;

  ConstraintDatabase& d_constraintDatabase;
  SetupLiteralCallBack d_setupLiteral;

  const ArithVariables& d_avariables;

  /** The equality engine being used by this class */
  eq::EqualityEngine* d_ee;
  /** The sat context */
  context::Context* d_satContext;
  /** The user context */
  context::UserContext* d_userContext;

  /** proof manager */
  ProofNodeManager* d_pnm;
  /** A proof generator for storing proofs of facts that are asserted to the EQ
   * engine. Note that these proofs **are not closed**; they may contain
   * literals from the explanation of their fact as unclosed assumptions.
   * This makes these proofs SAT-context depdent.
   *
   * This is why this generator is separate from the TheoryArithPrivate
   * generator, which stores closed proofs.
   */
  std::unique_ptr<EagerProofGenerator> d_pfGenEe;
  /** A proof generator for TrustNodes sent to TheoryArithPrivate.
   *
   * When TheoryArithPrivate requests an explanation from
   * ArithCongruenceManager, it can request a TrustNode for that explanation.
   * This proof generator is the one used in that TrustNode: it stores the
   * (closed) proofs of implications proved by the
   * ArithCongruenceManager/EqualityEngine.
   *
   * It is insufficient to just use the ProofGenerator from the ProofEqEngine,
   * since sometimes the ArithCongruenceManager needs to add some
   * arith-specific reasoning to extend the proof (e.g. rewriting the result
   * into a normal form).
   * */
  std::unique_ptr<EagerProofGenerator> d_pfGenExplain;

  /** Pointer to the proof equality engine of TheoryArith */
  theory::eq::ProofEqEngine* d_pfee;

  /** Raise a conflict node `conflict` to the theory of arithmetic.
   *
   * When proofs are enabled, a (closed) proof of the conflict should be
   * provided.
   */
  void raiseConflict(Node conflict, std::shared_ptr<ProofNode> pf = nullptr);
  /**
   * Are proofs enabled? This is true if a non-null proof manager was provided
   * to the constructor of this class.
   */
  bool isProofEnabled() const;

 public:
  bool inConflict() const;

  bool hasMorePropagations() const;

  const Node getNextPropagation();

  bool canExplain(TNode n) const;

private:
  Node externalToInternal(TNode n) const;

  void pushBack(TNode n);

  void pushBack(TNode n, TNode r);

  void pushBack(TNode n, TNode r, TNode w);

  bool propagate(TNode x);
  void explain(TNode literal, std::vector<TNode>& assumptions);

  /** Assert this literal to the eq engine. Common functionality for
   *   * assertionToEqualityEngine(..)
   *   * equalsConstant(c)
   *   * equalsConstant(lb, ub)
   * If proof is off, then just asserts.
   */
  void assertLitToEqualityEngine(Node lit,
                                 TNode reason,
                                 std::shared_ptr<ProofNode> pf);
  /** This sends a shared term to the uninterpreted equality engine. */
  void assertionToEqualityEngine(bool eq,
                                 ArithVar s,
                                 TNode reason,
                                 std::shared_ptr<ProofNode> pf);

  /** Check for proof for this or a symmetric fact
   *
   * The proof submitted to this method are stored in `d_pfGenEe`, and should
   * have closure properties consistent with the documentation for that member.
   *
   * @returns whether this or a symmetric fact has a proof.
   */
  bool hasProofFor(TNode f) const;
  /**
   * Sets the proof for this fact and the symmetric one.
   *
   * The proof submitted to this method are stored in `d_pfGenEe`, and should
   * have closure properties consistent with the documentation for that member.
   * */
  void setProofFor(TNode f, std::shared_ptr<ProofNode> pf) const;

  /** Dequeues the delay queue and asserts these equalities.*/
  void enableSharedTerms();
  void dequeueLiterals();

  void enqueueIntoNB(const std::set<TNode> all, NodeBuilder& nb);

  /**
   * Determine an explaination for `internal`. That is a conjunction of theory
   * literals which imply `internal`.
   *
   * The TrustNode here is a trusted propagation.
   */
  TrustNode explainInternal(TNode internal);

 public:
  ArithCongruenceManager(context::Context* satContext,
                         context::UserContext* u,
                         ConstraintDatabase&,
                         SetupLiteralCallBack,
                         const ArithVariables&,
                         RaiseEqualityEngineConflict raiseConflict,
                         ProofNodeManager* pnm);
  ~ArithCongruenceManager();

  //--------------------------------- initialization
  /**
   * Returns true if we need an equality engine, see
   * Theory::needsEqualityEngine.
   */
  bool needsEqualityEngine(EeSetupInfo& esi);
  /**
   * Finish initialize. This class is instructed by TheoryArithPrivate to use
   * the equality engine ee and proof equality engine pfee.
   */
  void finishInit(eq::EqualityEngine* ee, eq::ProofEqEngine* pfee);
  //--------------------------------- end initialization

  /**
   * Return the trust node for the explanation of literal. The returned
   * trust node is generated by the proof equality engine of this class.
   */
  TrustNode explain(TNode literal);

  void explain(TNode lit, NodeBuilder& out);

  void addWatchedPair(ArithVar s, TNode x, TNode y);

  inline bool isWatchedVariable(ArithVar s) const {
    return d_watchedVariables.isMember(s);
  }

  /** Assert an equality. */
  void watchedVariableIsZero(ConstraintCP eq);

  /** Assert a conjunction from lb and ub. */
  void watchedVariableIsZero(ConstraintCP lb, ConstraintCP ub);

  /** Assert that the value cannot be zero. */
  void watchedVariableCannotBeZero(ConstraintCP c);

  /** Assert that the value cannot be zero. */
  void watchedVariableCannotBeZero(ConstraintCP c, ConstraintCP d);


  /** Assert that the value is congruent to a constant. */
  void equalsConstant(ConstraintCP eq);
  void equalsConstant(ConstraintCP lb, ConstraintCP ub);

 private:
  class Statistics {
  public:
    IntStat d_watchedVariables;
    IntStat d_watchedVariableIsZero;
    IntStat d_watchedVariableIsNotZero;

    IntStat d_equalsConstantCalls;

    IntStat d_propagations;
    IntStat d_propagateConstraints;
    IntStat d_conflicts;

    Statistics();
  } d_statistics;

};/* class ArithCongruenceManager */

std::vector<Node> andComponents(TNode an);

}  // namespace arith
}  // namespace theory
}  // namespace cvc5
