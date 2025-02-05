/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Amalee Wilson, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
#include "prop/sat_solver_types.h"
#include "theory/output_channel.h"
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
   * postsolve, called at the end of each check-sat.
   */
  virtual void postsolve(prop::SatValue result);
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
   * @param id The inference identifier of the lemma
   * @param p The property of the lemma
   * @param skAsserts The skolem assertions for the given lemma
   * @param sks The skolems for each assertion in skAsserts.
   */
  virtual void notifyLemma(TNode n,
                           InferenceId id,
                           LemmaProperty p,
                           const std::vector<Node>& skAsserts,
                           const std::vector<Node>& sks);
  /** Needs candidate model, return true if the method below requires calling */
  virtual bool needsCandidateModel();
  /** Notify that m is a (candidate) model */
  virtual void notifyCandidateModel(TheoryModel* m);
  /** Get the theory identifier */
  TheoryId getId() const;

 protected:
  /** The output channel, for sending lemmas */
  OutputChannel d_out;
  /** The name */
  std::string d_name;

 private:
  /** Static allocator of theory module identifiers */
  static size_t d_idCounter;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__RELEVANCE_MANAGER__H */
