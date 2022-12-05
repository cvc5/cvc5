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
#include "theory/engine_output_channel.h"
#include "theory/theory.h"

namespace cvc5::internal {

class TheoryEngine;

namespace theory {

class TheoryModel;

/**
 * A theory engine module shares some functionality with a theory solver
 * but is not associated with a theory.
 */
class TheoryEngineModule : protected EnvObj
{
 public:
  /**
   * @param env The environment
   * @param engine The parent theory engine
   */
  TheoryEngineModule(Env& env, TheoryEngine* engine, const std::string& name);
  virtual ~TheoryEngineModule(){}
  /**
   * check, called at the beginning of a check in TheoryEngine.
   */
  virtual void check(Theory::Effort effort);
  /**
   * postCheck, called at the end of a check in TheoryEngine.
   */
  virtual void postCheck(Theory::Effort effort);
  /** Notify that a lemma was sent */
  virtual void notifyLemma(TNode n,
                           theory::LemmaProperty p,
                           const std::vector<Node>& skAsserts,
                           const std::vector<Node>& sks);
  /** Notify that m is a (candidate) model */
  virtual void notifyCandidateModel(TheoryModel* m);
  /** Get name, for debugging and statistics. */
  const std::string& getName();

 protected:
  /** The output channel, for sending lemmas */
  EngineOutputChannel d_out;
  /** The name */
  std::string d_name;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__RELEVANCE_MANAGER__H */
