/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Virtual class for theory engine modules
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__THEORY_ENGINE_MODULE_H
#define CVC5__THEORY__THEORY_ENGINE_MODULE_H

#include "expr/node.h"
#include "theory/theory.h"

namespace cvc5::internal {
namespace theory {

class TheoryModel;

/**
 */
class TheoryEngineModule : protected EnvObj
{
  
 public:
  /**
   * @param env The environment
   */
  TheoryEngineModule(Env& env);
  /**
   * check, called at the beginning of a check in TheoryEngine.
   */
  virtual void check(Theory::Effort effort);
  /** 
   * postCheck, called at the end of a check in TheoryEngine.
   */
  virtual void postCheck();
  /** Notify lemma, for difficulty measurements */
  virtual void notifyLemma(TNode n);
  /** Notify that m is a (candidate) model, for difficulty measurements */
  virtual void notifyCandidateModel(TheoryModel* m);
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__RELEVANCE_MANAGER__H */
