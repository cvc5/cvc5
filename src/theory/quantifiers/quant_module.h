/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * quantifier module
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANT_MODULE_H
#define CVC5__THEORY__QUANT_MODULE_H

#include <iostream>
#include <map>
#include <vector>

#include "smt/env_obj.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/quantifiers_registry.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
class TermDb;
}  // namespace quantifiers

/** QuantifiersModule class
 *
 * This is the virtual class for defining subsolvers of the quantifiers theory.
 * It has a similar interface to a Theory object.
 */
class QuantifiersModule : protected EnvObj
{
 public:
  /** effort levels for quantifiers modules check */
  enum QEffort
  {
    // conflict effort, for conflict-based instantiation
    QEFFORT_CONFLICT,
    // standard effort, for heuristic instantiation
    QEFFORT_STANDARD,
    // model effort, for model-based instantiation
    QEFFORT_MODEL,
    // last call effort, for last resort techniques
    QEFFORT_LAST_CALL,
    // none
    QEFFORT_NONE,
  };

 public:
  QuantifiersModule(Env& env,
                    quantifiers::QuantifiersState& qs,
                    quantifiers::QuantifiersInferenceManager& qim,
                    quantifiers::QuantifiersRegistry& qr,
                    quantifiers::TermRegistry& tr);
  virtual ~QuantifiersModule() {}
  /** Presolve.
   *
   * Called at the beginning of check-sat call.
   */
  virtual void presolve() {}
  /** Needs check.
   *
   * Returns true if this module wishes a call to be made
   * to check(e) during QuantifiersEngine::check(e).
   */
  virtual bool needsCheck(Theory::Effort e)
  {
    return e >= Theory::EFFORT_LAST_CALL;
  }
  /** Needs model.
   *
   * Whether this module needs a model built during a
   * call to QuantifiersEngine::check(e)
   * It returns one of QEFFORT_* from the enumeration above.
   * which specifies the quantifiers effort in which it requires the model to
   * be built.
   */
  virtual QEffort needsModel(Theory::Effort e);
  /** Reset.
   *
   * Called at the beginning of QuantifiersEngine::check(e).
   */
  virtual void reset_round(Theory::Effort e) {}
  /** Check.
   *
   *   Called during QuantifiersEngine::check(e) depending
   *   if needsCheck(e) returns true.
   */
  virtual void check(Theory::Effort e, QEffort quant_e) = 0;
  /** Check complete?
   *
   * Returns false if the module's reasoning was globally incomplete
   * (e.g. "sat" must be replaced with "incomplete").
   *
   * This is called just before the quantifiers engine will return
   * with no lemmas added during a LAST_CALL effort check.
   *
   * If this method returns false, it should update incId to the reason for
   * why the module was incomplete.
   */
  virtual bool checkComplete(IncompleteId& incId) { return true; }
  /** Check was complete for quantified formula q
   *
   * If for each quantified formula q, some module returns true for
   * checkCompleteFor( q ),
   * and no lemmas are added by the quantifiers theory, then we may answer
   * "sat", unless
   * we are incomplete for other reasons.
   */
  virtual bool checkCompleteFor(Node q) { return false; }
  /** Check ownership
   *
   * Called once for new quantified formulas that are registered by the
   * quantifiers theory. The primary purpose of this function is to establish
   * if this module is the owner of quantified formula q.
   */
  virtual void checkOwnership(Node q) {}
  /** Register quantifier
   *
   * Called once for new quantified formulas q that are pre-registered by the
   * quantifiers theory, after internal ownership of quantified formulas is
   * finalized. This does context-independent initialization of this module
   * for quantified formula q.
   */
  virtual void registerQuantifier(Node q) {}
  /** Pre-register quantifier
   *
   * Called once for new quantified formulas that are
   * pre-registered by the quantifiers theory, after
   * internal ownership of quantified formulas is finalized.
   */
  virtual void preRegisterQuantifier(Node q) {}
  /** Assert node.
   *
   * Called when a quantified formula q is asserted to the quantifiers theory
   */
  virtual void assertNode(Node q) {}
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  virtual std::string identify() const = 0;
  //----------------------------general queries
  /** get currently used the equality engine */
  eq::EqualityEngine* getEqualityEngine() const;
  /** are n1 and n2 equal in the current used equality engine? */
  bool areEqual(TNode n1, TNode n2) const;
  /** are n1 and n2 disequal in the current used equality engine? */
  bool areDisequal(TNode n1, TNode n2) const;
  /** get the representative of n in the current used equality engine */
  TNode getRepresentative(TNode n) const;
  /** get currently used term database */
  quantifiers::TermDb* getTermDatabase() const;
  /** get the quantifiers state */
  quantifiers::QuantifiersState& getState();
  /** get the quantifiers inference manager */
  quantifiers::QuantifiersInferenceManager& getInferenceManager();
  /** get the quantifiers registry */
  quantifiers::QuantifiersRegistry& getQuantifiersRegistry();
  /** get the term registry */
  quantifiers::TermRegistry& getTermRegistry();
  //----------------------------end general queries
 protected:
  /** Reference to the state of the quantifiers engine */
  quantifiers::QuantifiersState& d_qstate;
  /** Reference to the quantifiers inference manager */
  quantifiers::QuantifiersInferenceManager& d_qim;
  /** Reference to the quantifiers registry */
  quantifiers::QuantifiersRegistry& d_qreg;
  /** Reference to the term registry */
  quantifiers::TermRegistry& d_treg;
}; /* class QuantifiersModule */

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANT_UTIL_H */
