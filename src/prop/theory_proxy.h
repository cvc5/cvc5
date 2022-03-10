/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Dejan Jovanovic, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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
#include "expr/node.h"
#include "proof/trust_node.h"
#include "prop/registrar.h"
#include "prop/sat_solver_types.h"
#include "smt/env_obj.h"
#include "theory/theory.h"
#include "theory/theory_preprocessor.h"
#include "util/resource_manager.h"

namespace cvc5 {

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
              decision::DecisionEngine* decisionEngine,
              SkolemDefManager* skdm);

  ~TheoryProxy();

  /** Finish initialize */
  void finishInit(CnfStream* cnfStream);

  /** Presolve, which calls presolve for the modules managed by this class */
  void presolve();

  /**
   * Notifies this module of the input assertions.
   * @param assertion The preprocessed input assertions,
   * @param skolemMap Map from indices in assertion to the Skolem they are
   * the definition for
   * @param ppl The preprocessed learned literals, that is, the literals that
   * hold at top-level, as computed by the circuit propagator.
   */
  void notifyInputFormulas(const std::vector<Node>& assertions,
                           std::unordered_map<size_t, Node>& skolemMap,
                           const std::vector<Node>& ppl);
  /**
   * Notify a lemma or input assertion, possibly corresponding to a skolem
   * definition.
   */
  void notifyAssertion(Node lem,
                       TNode skolem = TNode::null(),
                       bool isLemma = false);

  void theoryCheck(theory::Theory::Effort effort);

  void explainPropagation(SatLiteral l, SatClause& explanation);

  void theoryPropagate(SatClause& output);

  void enqueueTheoryLiteral(const SatLiteral& l);

  SatLiteral getNextTheoryDecisionRequest();

  SatLiteral getNextDecisionEngineRequest(bool& stopSearch);

  bool theoryNeedCheck() const;

  /** Is incomplete */
  bool isIncomplete() const;

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
  /** Preregister term */
  void preRegister(Node n) override;

  /** Get the zero-level assertions */
  std::vector<Node> getLearnedZeroLevelLiterals() const;

 private:
  /** The prop engine we are using. */
  PropEngine* d_propEngine;

  /** The CNF engine we are using. */
  CnfStream* d_cnfStream;

  /** The decision engine we are using. */
  decision::DecisionEngine* d_decisionEngine;

  /**
   * Whether the decision engine needs notification of active skolem
   * definitions, see DecisionEngine::needsActiveSkolemDefs.
   */
  bool d_dmNeedsActiveDefs;

  /** The theory engine we are using. */
  TheoryEngine* d_theoryEngine;

  /** Queue of asserted facts */
  context::CDQueue<TNode> d_queue;

  /**
   * Set of all lemmas that have been "shared" in the portfolio---i.e.,
   * all imported and exported lemmas.
   */
  std::unordered_set<Node> d_shared;

  /** The theory preprocessor */
  theory::TheoryPreprocessor d_tpp;

  /** The skolem definition manager */
  SkolemDefManager* d_skdm;

  /** The zero level learner */
  std::unique_ptr<ZeroLevelLearner> d_zll;

}; /* class TheoryProxy */

}  // namespace prop
}  // namespace cvc5

#endif
