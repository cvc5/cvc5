/*********************                                                        */
/*! \file mcsat.h
 ** \verbatim
 ** Original author: dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief SmtEngine: the main public entry point of libcvc4.
 **
 ** SmtEngine: the main public entry point of libcvc4.
 **/

#pragma once

#include "cvc4_public.h"

#include "expr/expr.h"
#include "util/statistics.h"

namespace CVC4 {

class ExprManager;
class SmtEngine;

namespace context {
  class UserContext;
  class Context;
}

namespace mcsat {

class Solver;

class CVC4_PUBLIC MCSatEngine {

  /** Expression manager to use */
  ExprManager* d_exprManager;

  /** SmtEngine (needed for weird reasons) */
  SmtEngine* d_smtEngine;

  /** The user context the solver */
  context::UserContext* d_userContext;

  /** The search context of the solver */
  context::Context* d_searchContext;

  /** Actual solver */
  Solver* d_mcSolver;

public:

  /**
   * Construct an SmtEngine with the given expression manager.
   */
  MCSatEngine(ExprManager* em) throw();

  /**
   * Destruct the SMT engine.
   */
  ~MCSatEngine() throw();

  /**
   * Assert the formula to the solver. If process is false the assertion will be
   * processed only after the call to check().
   * @param assertion the assertion
   * @param process true if to be processed as soon as possible
   */
  void addAssertion(Expr assertion, bool process);

  /** Check if the current set of assertions is satisfiable */
  bool check();

  /** Export statistics from this SmtEngine. */
  Statistics getStatistics() const throw();

};/* class MCSatEngine */

} /* mcsat namespace */
}/* CVC4 namespace */

