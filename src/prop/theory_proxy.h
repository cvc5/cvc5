/*********************                                                        */
/*! \file theory_proxy.h
 ** \verbatim
 ** Original author: Dejan Jovanovic
 ** Major contributors: Liana Hadarean, Morgan Deters
 ** Minor contributors (to current version): Christopher L. Conway, Tim King, Kshitij Bansal
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief SAT Solver.
 **
 ** SAT Solver.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PROP__SAT_H
#define __CVC4__PROP__SAT_H

// Just defining this for now, since there's no other SAT solver bindings.
// Optional blocks below will be unconditionally included
#define __CVC4_USE_MINISAT

#include "theory/theory.h"
#include "util/statistics_registry.h"

#include "context/cdqueue.h"

#include "prop/sat_solver.h"

namespace CVC4 {

class DecisionEngine;
class TheoryEngine;

namespace prop {

class PropEngine;
class CnfStream;

/**
 * The proxy class that allows the SatSolver to communicate with the theories
 */
class TheoryProxy {

  /** The prop engine we are using */
  PropEngine* d_propEngine;

  /** The CNF engine we are using */
  CnfStream* d_cnfStream;

  /** The decision engine we are using */
  DecisionEngine* d_decisionEngine;

  /** The theory engine we are using */
  TheoryEngine* d_theoryEngine;

  /** Context we will be using to synchronzie the sat solver */
  context::Context* d_context;

  /** Queue of asserted facts */
  context::CDQueue<TNode> d_queue;

  /**
   * Set of all lemmas that have been "shared" in the portfolio---i.e.,
   * all imported and exported lemmas.
   */
  std::hash_set<Node, NodeHashFunction> d_shared;

  /**
   * Statistic: the number of replayed decisions (via --replay).
   */
  KEEP_STATISTIC(IntStat, d_replayedDecisions,
                 "prop::theoryproxy::replayedDecisions", 0);

public:
  TheoryProxy(PropEngine* propEngine,
              TheoryEngine* theoryEngine,
              DecisionEngine* decisionEngine,
              context::Context* context,
              CnfStream* cnfStream);

  ~TheoryProxy();


  void theoryCheck(theory::Theory::Effort effort);

  void explainPropagation(SatLiteral l, SatClause& explanation);

  void theoryPropagate(SatClause& output);

  void enqueueTheoryLiteral(const SatLiteral& l);

  SatLiteral getNextTheoryDecisionRequest();

  SatLiteral getNextDecisionEngineRequest(bool& stopSearch);

  bool theoryNeedCheck() const;

  /**
   * Notifies of a new variable at a decision level.
   */
  void variableNotify(SatVariable var);

  TNode getNode(SatLiteral lit);

  void notifyRestart();

  void notifyNewLemma(SatClause& lemma);

  SatLiteral getNextReplayDecision();

  void logDecision(SatLiteral lit);

  void checkTime();

  bool isDecisionEngineDone();

  bool isDecisionRelevant(SatVariable var);

  SatValue getDecisionPolarity(SatVariable var);

};/* class SatSolver */

/* Functions that delegate to the concrete SAT solver. */

inline TheoryProxy::TheoryProxy(PropEngine* propEngine,
                                TheoryEngine* theoryEngine,
                                DecisionEngine* decisionEngine,
                                context::Context* context,
                                CnfStream* cnfStream) :
  d_propEngine(propEngine),
  d_cnfStream(cnfStream),
  d_decisionEngine(decisionEngine),
  d_theoryEngine(theoryEngine),
  d_context(context),
  d_queue(context)
{}

}/* CVC4::prop namespace */

}/* CVC4 namespace */

#endif /* __CVC4__PROP__SAT_H */
