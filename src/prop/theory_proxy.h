/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * SAT Solver.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__SAT_H
#define CVC5__PROP__SAT_H

#include <unordered_set>

#include "context/cdhashset.h"
#include "context/cdqueue.h"
#include "decision/decision_engine.h"
#include "expr/node.h"
#include "proof/trust_node.h"
#include "prop/learned_db.h"
#include "prop/lemma_inprocess.h"
#include "prop/registrar.h"
#include "prop/sat_solver_types.h"
#include "prop/theory_preregistrar.h"
#include "smt/env_obj.h"
#include "theory/incomplete_id.h"
#include "theory/theory.h"
#include "theory/theory_preprocessor.h"
#include "util/resource_manager.h"

namespace cvc5::internal {

class Env;
class TheoryEngine;

namespace decision {
class DecisionEngine;
}

namespace prop {

class PropEngine;
class CnfStream;
class SkolemDefManager;
class ZeroLevelLearner;

/**
 * The proxy class that allows the SatSolver to communicate with the theories
 */
class TheoryProxy : protected EnvObj, public Registrar
{
  using NodeSet = context::CDHashSet<Node>;

 public:
  TheoryProxy(Env& env,
              PropEngine* propEngine,
              TheoryEngine* theoryEngine,
              SkolemDefManager* skdm);

  ~TheoryProxy();

  /** Finish initialize */
  void finishInit(CDCLTSatSolver* ss, CnfStream* cs);

  /** Presolve, which calls presolve for the modules managed by this class */
  void presolve();
  /** Postsolve, which calls postsolve for the modules managed by this class */
  void postsolve(SatValue result);

  /**
   * Notify that lhs was substituted by rhs during preprocessing. This impacts
   * the tracked learned literals and output traces.
   * @param lhs The left-hand side of the substitution
   * @param rhs The right-hand side of the substitution
   */
  void notifyTopLevelSubstitution(const Node& lhs, const Node& rhs) const;
  /**
   * Notifies this module of the input assertions.
   * @param assertion The preprocessed input assertions,
   * @param skolemMap Map from indices in assertion to the Skolem they are
   * the definition for
   */
  void notifyInputFormulas(const std::vector<Node>& assertions,
                           std::unordered_map<size_t, Node>& skolemMap);
  /**
   * Notify that lem is a skolem definition for the given skolem. This is called
   * before pushing the lemma to the SAT solver.
   */
  void notifySkolemDefinition(Node lem, TNode skolem);
  /**
   * Notify a lemma or input assertion, possibly corresponding to a skolem
   * definition. This is called after pushing the lemma to the SAT solver.
   */
  void notifyAssertion(Node lem,
                       TNode skolem = TNode::null(),
                       bool isLemma = false,
                       bool local = false);

  void theoryCheck(theory::Theory::Effort effort);

  /** Get an explanation for literal `l` and save it on clause `explanation`. */
  void explainPropagation(SatLiteral l, SatClause& explanation);
  /**
   * Notify SAT clause. This should be called whenever the SAT solver learns
   * a SAT clause. It notifies user plugins of the added clauses.
   */
  void notifySatClause(const SatClause& clause);

  void theoryPropagate(SatClause& output);

  void enqueueTheoryLiteral(const SatLiteral& l);

  /**
   * Get the next decision request.
   *
   * This first queries the theory engine for a decision request. If the theory
   * engine does not request a decision, the decision engine is queried.
   *
   * If `requirePhase` is true, the decision must be decided as is, in the
   * given polarity. Else it should respect the polarity configured via
   * PropEngine::requirePhase, if any.
   *
   * @param requirePhase True if the returned SatLiteral must be decided
   *                     as-is, in its given polarity.
   * @param stopSearch   True if the current search should be terminated. In
   *                     this case, lit_Undef is returned.
   * @return The next decision.
   */
  SatLiteral getNextDecisionRequest(bool& requirePhase, bool& stopSearch);

  bool theoryNeedCheck() const;

  /** Is model unsound */
  bool isModelUnsound() const;
  /** Is refutation unsound */
  bool isRefutationUnsound() const;
  /** Get model unsound id, valid when isModelUnsound is true. */
  theory::IncompleteId getModelUnsoundId() const;
  /** Get unsound id, valid when isRefutationUnsound is true. */
  theory::IncompleteId getRefutationUnsoundId() const;

  TNode getNode(SatLiteral lit);

  void notifyRestart();

  void spendResource(Resource r);

  bool isDecisionEngineDone();

  /**
   * Get the associated CNF stream.
   * @return The CNF stream.
   */
  CnfStream* getCnfStream() const;

  /**
   * Call the preprocessor on node, return trust node corresponding to the
   * rewrite.
   */
  TrustNode preprocessLemma(TrustNode trn,
                            std::vector<theory::SkolemLemma>& newLemmas);
  /**
   * Call the preprocessor on node, return trust node corresponding to the
   * rewrite.
   */
  TrustNode preprocess(TNode node, std::vector<theory::SkolemLemma>& newLemmas);
  /**
   * Remove ITEs from the node.
   */
  TrustNode removeItes(TNode node, std::vector<theory::SkolemLemma>& newLemmas);
  /**
   * Get the skolems within node and their corresponding definitions, store
   * them in sks and skAsserts respectively. Note that this method does not
   * necessary include all of the skolems in skAsserts. In other words, it
   * collects from node only. To compute all skolems that node depends on
   * requires calling this method again on each lemma in skAsserts until a
   * fixed point is reached.
   */
  void getSkolems(TNode node,
                  std::vector<Node>& skAsserts,
                  std::vector<Node>& sks);
  /**
   * Called when a SAT literal for atom n has been allocated in the SAT solver.
   */
  void notifySatLiteral(Node n) override;

  /**
   * Callback to notify that the SAT solver backtracked.
   */
  void notifyBacktrack();

  /** Get the zero-level assertions */
  std::vector<Node> getLearnedZeroLevelLiterals(
      modes::LearnedLitType ltype) const;
  /** Get the zero-level assertions that should be used on deep restart */
  std::vector<Node> getLearnedZeroLevelLiteralsForRestart() const;
  /** Get literal type using ZLL utility */
  modes::LearnedLitType getLiteralType(const Node& lit) const;

  /** Inprocess lemma */
  TrustNode inprocessLemma(TrustNode& trn);

 private:
  /** The prop engine we are using. */
  PropEngine* d_propEngine;

  /** The CNF engine we are using. */
  CnfStream* d_cnfStream;

  /** The decision engine we will be using */
  std::unique_ptr<decision::DecisionEngine> d_decisionEngine;

  /**
   * True if we need to track active skolem definitions for the preregistrar,
   * false to track for the decision engine.
   */
  bool d_trackActiveSkDefs;
  /**
   * Whether the decision engine needs to track active skolem definitions as
   * local assertions.
   */
  bool d_dmTrackActiveSkDefs;
  /**
   * Are we in solve?
   * This is true if there was a call to presolve() after the last call to
   * postsolve(), if any.
   */
  bool d_inSolve;

  /** The theory engine we are using. */
  TheoryEngine* d_theoryEngine;

  /** Queue of asserted facts and their decision level. */
  context::CDQueue<std::pair<TNode, int32_t>> d_queue;

  /** The theory preprocessor */
  theory::TheoryPreprocessor d_tpp;

  /** The skolem definition manager */
  SkolemDefManager* d_skdm;

  /** The zero level learner */
  std::unique_ptr<ZeroLevelLearner> d_zll;

  /** The inprocess utility */
  std::unique_ptr<LemmaInprocess> d_lemip;

  /** Preregister policy */
  std::unique_ptr<TheoryPreregistrar> d_prr;

  /** Whether we have been requested to stop the search */
  context::CDO<bool> d_stopSearch;

  /**
   * Whether we activated new skolem definitions on the last call to
   * theoryCheck. If this is true, then theoryNeedCheck must return true,
   * since there are new formulas to satisfy. Note that skolem definitions
   * are dynamically activated only when decision=justification.
   */
  bool d_activatedSkDefs;
}; /* class TheoryProxy */

}  // namespace prop
}  // namespace cvc5::internal

#endif
