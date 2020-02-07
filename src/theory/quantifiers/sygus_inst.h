/*********************                                                        */
/*! \file sygus_inst.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief SyGuS instantiator class.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS_INST_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS_INST_H

#include <unordered_map>
#include <unordered_set>

#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace quantifiers {

class SygusInst : public QuantifiersModule
{
 public:
  SygusInst(QuantifiersEngine* qe);
  ~SygusInst() = default;

  /** Presolve.
   *
   * Called at the beginning of check-sat call.
   */
  // void presolve() {}
  /** Needs check.
   *
   * Returns true if this module wishes a call to be made
   * to check(e) during QuantifiersEngine::check(e).
   */
  // bool needsCheck( Theory::Effort e ) { return e>=Theory::EFFORT_LAST_CALL; }
  /** Needs model.
   *
   * Whether this module needs a model built during a
   * call to QuantifiersEngine::check(e)
   * It returns one of QEFFORT_* from quantifiers_engine.h,
   * which specifies the quantifiers effort in which it requires the model to
   * be built.
   */
  // QEffort needsModel(Theory::Effort e);
  /** Reset.
   *
   * Called at the beginning of QuantifiersEngine::check(e).
   */
  // void reset_round( Theory::Effort e ){}
  /** Check.
   *
   *   Called during QuantifiersEngine::check(e) depending
   *   if needsCheck(e) returns true.
   */
  void check(Theory::Effort e, QEffort quant_e) override;
  /** Check complete?
   *
   * Returns false if the module's reasoning was globally incomplete
   * (e.g. "sat" must be replaced with "incomplete").
   *
   * This is called just before the quantifiers engine will return
   * with no lemmas added during a LAST_CALL effort check.
   */
  // bool checkComplete() { return true; }
  /** Check was complete for quantified formula q
   *
   * If for each quantified formula q, some module returns true for
   * checkCompleteFor( q ),
   * and no lemmas are added by the quantifiers theory, then we may answer
   * "sat", unless
   * we are incomplete for other reasons.
   */
  // bool checkCompleteFor( Node q ) { return false; }
  /** Check ownership
   *
   * Called once for new quantified formulas that are registered by the
   * quantifiers theory. The primary purpose of this function is to establish
   * if this module is the owner of quantified formula q.
   */
  // void checkOwnership(Node q) {}
  /** Register quantifier
   *
   * Called once for new quantified formulas q that are pre-registered by the
   * quantifiers theory, after internal ownership of quantified formulas is
   * finalized. This does context-dependent initialization of this module.
   */
  void registerQuantifier(Node q) override;
  /** Pre-register quantifier
   *
   * Called once for new quantified formulas that are
   * pre-registered by the quantifiers theory, after
   * internal ownership of quantified formulas is finalized.
   */
  void preRegisterQuantifier(Node q) override;
  /** Assert node.
   *
   * Called when a quantified formula q is asserted to the quantifiers theory
   */
  // void assertNode(Node q) override;
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  std::string identify() const override { return "SygusInst"; }

 private:
  std::unordered_map<Node,
                     std::unordered_set<TNode, TNodeHashFunction>,
                     NodeHashFunction>
      d_quant_vars;
  std::unordered_map<Node, std::unique_ptr<SygusEnumerator>, NodeHashFunction>
      d_enumerators;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif
