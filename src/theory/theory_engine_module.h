/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
 *
 * A theory engine module is allowed to send lemmas or conflicts via its
 * output channel (d_out) during check and postCheck.
 */
class TheoryEngineModule : protected EnvObj
{
 public:
  /**
   * @param env The environment
   * @param engine The parent theory engine
   */
  TheoryEngineModule(Env& env, TheoryEngine* engine, const std::string& name);
  virtual ~TheoryEngineModule() {}
  /**
   * presolve, called at the beginning of each check-sat.
   */
  virtual void presolve();
  /**
   * check, called at the beginning of a check in TheoryEngine.
   */
  virtual void check(Theory::Effort effort);
  /**
   * postCheck, called at the end of a check in TheoryEngine.
   */
  virtual void postCheck(Theory::Effort effort);
  /**
   * Notify that a lemma was sent
   *
   * @param n The lemma, which has been theory preprocessed
   * @param p The property of the lemma
   * @param skAsserts The skolem assertions for the given lemma
   * @param sks The skolems for each assertion in skAsserts.
   */
  virtual void notifyLemma(TNode n,
                           theory::LemmaProperty p,
                           const std::vector<Node>& skAsserts,
                           const std::vector<Node>& sks);
  /** Needs candidate model, return true if the method below requires calling */
  virtual bool needsCandidateModel();
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
