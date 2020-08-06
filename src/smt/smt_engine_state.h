/*********************                                                        */
/*! \file smt_engine_state.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utility for maintaining the state of the SMT engine.
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__SMT_ENGINE_STATE_H
#define CVC4__SMT__SMT_ENGINE_STATE_H

#include <string>

#include "context/cdhashmap.h"
#include "expr/node.h"

namespace CVC4 {
  
class SmtEngine;

namespace smt {

/**
 * This utility is responsible for maintaining names for expressions.
 */
class SmtEngineState
{
 public:
  SmtEngineState(SmtEngine& smt);
  ~SmtEngineState(){}
  
  void notifyCheckSat();
  void notifyCheckSatResult(Result r);
  
  void internalPush();

  void internalPop(bool immediate = false);
  
  /** Get a pointer to the UserContext owned by this SmtEngine. */
  context::UserContext* getUserContext();

  /** Get a pointer to the Context owned by this SmtEngine. */
  context::Context* getContext();
  
 private:
  /** Reference to the SmtEngine */
  SmtEngine& d_smt;
  /** Expr manager context */
  std::unique_ptr<context::Context> d_context;
  /** User level context */
  std::unique_ptr<context::UserContext> d_userContext;
  /** The context levels of user pushes */
  std::vector<int> d_userLevels;

  /**
   * Number of internal pops that have been deferred.
   */
  unsigned d_pendingPops;

  /**
   * Whether or not this SmtEngine is fully initialized (post-construction).
   * This post-construction initialization is automatically triggered by the
   * use of the SmtEngine; e.g. when the first formula is asserted, a call
   * to simplify() is issued, a scope is pushed, etc.
   */
  bool d_fullyInited;

  /**
   * Whether or not a checkEntailed() or checkSatisfiability() has already been
   * made through this SmtEngine.  If true, and incrementalSolving is false,
   * then attempting an additional checkEntailed() or checkSat() will fail with
   * a ModalException.
   */
  bool d_queryMade;

  /**
   * Internal status flag to indicate whether we've sent a theory
   * presolve() notification and need to match it with a postsolve().
   */
  bool d_needPostsolve;

  /**
   * Most recent result of last checkSatisfiability/checkEntailed or
   * (set-info :status).
   */
  Result d_status;

  /**
   * The expected status of the next satisfiability check.
   */
  Result d_expectedStatus;

  /** 
   * The SMT mode  TODO
   */
  SmtMode d_smtMode;

  /**
   * The input file name (if any) or the name set through setInfo (if any)
   */
  std::string d_filename;
};

}  // namespace smt
}  // namespace CVC4

#endif
