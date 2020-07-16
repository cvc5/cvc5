/*********************                                                        */
/*! \file assertions_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for managing assertions for an SMT engine.
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__ASSERTIONS_MANAGER_H
#define CVC4__SMT__ASSERTIONS_MANAGER_H

#include <map>

#include "smt/process_assertions.h"
#include "smt/abstract_values.h"

namespace CVC4 {

class SmtEngine;

namespace smt {

/**
 * Module in charge of assertions for an SMT engine.
 */
class AssertionsManager
{
 public:
   AssertionsManager(SmtEngine& smt, ResourceManager& rm);
  ~AssertionsManager();
  /** finish init */
  void finishInit();
 private:
  /** Reference to the SMT engine */
  SmtEngine& d_smt;
  /** Reference to resource manager */
  ResourceManager& d_resourceManager;
  /** The assertions processor */
  ProcessAssertions d_proc;
  /** The abstract values utility */
  /**
   * The assertion list (before any conversion) for supporting
   * getAssertions().  Only maintained if in incremental mode.
   */
  AssertionList* d_assertionList;

  /**
   * List of lemmas generated for global recursive function definitions. We
   * assert this list of definitions in each check-sat call.
   */
  std::unique_ptr<std::vector<Node>> d_globalDefineFunRecLemmas;

  /**
   * The list of assumptions from the previous call to checkSatisfiability.
   * Note that if the last call to checkSatisfiability was an entailment check,
   * i.e., a call to checkEntailed(a1, ..., an), then d_assumptions contains
   * one single assumption ~(a1 AND ... AND an).
   */
  std::vector<Node> d_assumptions;
  /*
   * Whether we did a global negation of the formula.
   */
  bool d_globalNegation;
};

}  // namespace smt
}  // namespace CVC4

#endif
