/*********************                                                        */
/*! \file justification_strategy.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Justification strategy
 **/

#include "cvc4_private.h"

#ifndef CVC4__DECISION__JUSTIFICATION_STRATEGY_H
#define CVC4__DECISION__JUSTIFICATION_STRATEGY_H

#include "expr/node.h"
#include "prop/cnf_stream.h"
#include "prop/sat_solver.h"
#include "prop/sat_solver_types.h"
#include "decision/assertion_list.h"

namespace CVC4 {

class JustificationStrategy
{
 public:
  /** Constructor */
  JustificationStrategy(context::Context* c,
                 context::UserContext* u);

  /** Finish initialize */
  void finishInit(prop::CDCLTSatSolverInterface* ss, prop::CnfStream* cs);

  /** Gets the next decision based on strategies that are enabled */
  prop::SatLiteral getNext(bool& stopSearch);

  /** Is the DecisionEngine in a state where it has solved everything? */
  bool isDone();

  /**
   * Notify this class that assertion is an (input) assertion, not corresponding
   * to a skolem definition.
   */
  void addAssertion(TNode assertion);
  /**
   * Notify this class that lem is an active assertion in this SAT context
   */
  void notifyRelevantSkolemAssertion(TNode lem);

  /** Interface to SAT solver */
  bool hasSatLiteral(TNode n);
  prop::SatLiteral getSatLiteral(TNode n);
  prop::SatValue getSatValue(prop::SatLiteral l);
  prop::SatValue getSatValue(TNode n);
  Node getNode(prop::SatLiteral l);

 private:
  /** SAT context */
  context::Context* d_satContext;
  /** User context */
  context::UserContext* d_userContext;
  /** CNF stream */
  prop::CnfStream* d_cnfStream;
  /** SAT solver */
  prop::CDCLTSatSolverInterface* d_satSolver;
  /** The assertions */
  AssertionList d_assertions;
  /** The skolem assertions */
  AssertionList d_skolemAssertions;
};

}/* CVC4 namespace */

#endif /* CVC4__DECISION__JUSTIFICATION_STRATEGY_H */
