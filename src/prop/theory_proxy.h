/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
  void postsolve();

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
                       bool isLemma = false);

  void theoryCheck(theory::Theory::Effort effort);

  /** Get an explanation for literal `l` and save it on clause `explanation`. */
  void explainPropagation(SatLiteral l, SatClause& explanation);
  /** Notify that current propagation inserted at lower level than current.
   *
   * This method should be called by the SAT solver when the explanation of the
   * current propagation is added at lower level than the current user level.
   * It'll trigger a call to the ProofCnfStream to notify it that the proof of
   * this propagation should be saved in case it's needed after this user
   * context is popped.
   */
  void notifyCurrPropagationInsertedAtLevel(int explLevel);
  /** Notify that added clause was inserted at lower level than current.
   *
   * As above, but for clauses asserted into the SAT solver. This cannot be done
   * in terms of "current added clause" because the clause added at a lower
   * level could be for example a lemma derived at a prior moment whose
   * assertion the SAT solver delayed.
   */
  void notifyClauseInsertedAtLevel(const SatClause& clause, int clLevel);

  void theoryPropagate(SatClause& output);

  void enqueueTheoryLiteral(const SatLiteral& l);

  SatLiteral getNextTheoryDecisionRequest();

  SatLiteral getNextDecisionEngineRequest(bool& stopSearch);

  bool theoryNeedCheck() const;

  /** Is model unsound */
  bool isModelUnsound() const;
  /** Is refutation unsound */
  bool isRefutationUnsound() const;
  /** Get model unsound id, valid when isModelUnsound is true. */
  theory::IncompleteId getModelUnsoundId() const;
  /** Get unsound id, valid when isRefutationUnsound is true. */
  theory::IncompleteId getRefutationUnsoundId() const;

  /**
   * Notifies of a new variable at a decision level.
   */
  void variableNotify(SatVariable var);

  TNode getNode(SatLiteral lit);

  void notifyRestart();

  void spendResource(Resource r);

  bool isDecisionEngineDone();

  bool isDecisionRelevant(SatVariable var);

  SatValue getDecisionPolarity(SatVariable var);

  CnfStream* getCnfStream();

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
   * Callback to notify that the SAT solver backtracked by the given number
   * of levels.
   */
  void notifyBacktrack(uint32_t nlevels);

  /** Get the zero-level assertions */
  std::vector<Node> getLearnedZeroLevelLiterals(
      modes::LearnedLitType ltype) const;
  /** Get the zero-level assertions that should be used on deep restart */
  std::vector<Node> getLearnedZeroLevelLiteralsForRestart() const;
  /** Get literal type using ZLL utility */
  modes::LearnedLitType getLiteralType(const Node& lit) const;

 private:
  /** The prop engine we are using. */
  PropEngine* d_propEngine;

  /** The CNF engine we are using. */
  CnfStream* d_cnfStream;

  /** The decision engine we will be using */
  std::unique_ptr<decision::DecisionEngine> d_decisionEngine;

  /**
   * Whether the decision engine needs notification of active skolem
   * definitions, see DecisionEngine::needsActiveSkolemDefs.
   */
  bool d_trackActiveSkDefs;

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
