/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Method for setting the default options of an SMT engine.
 */

#ifndef CVC5__SMT__SET_DEFAULTS_H
#define CVC5__SMT__SET_DEFAULTS_H

#include "options/options.h"
#include "theory/logic_info.h"

namespace cvc5 {
namespace smt {

/**
 * Class responsible for setting default options, which includes managing
 * implied options and dependencies between the options and the logic.
 */
class SetDefaults
{
 public:
  /**
   * @param isInternalSubsolver Whether we are setting the options for an
   * internal subsolver (see SmtEngine::isInternalSubsolver).
   */
  SetDefaults(bool isInternalSubsolver);
  /**
   * The purpose of this method is to set the default options and update the
   * logic info for an SMT engine.
   *
   * @param logic A reference to the logic of SmtEngine, which can be
   * updated by this method based on the current options and the logic itself.
   * @param opts The options to modify, typically the main options of the
   * SmtEngine in scope.
   */
  void setDefaults(LogicInfo& logic, Options& opts);

 private:
  //------------------------- utility methods
  /**
   * Determine whether we will be solving a SyGuS problem.
   */
  bool isSygus(const Options& opts) const;
  /**
   * Determine whether we will be using SyGuS.
   */
  bool usesSygus(const Options& opts) const;
  /**
   * Check if incompatible with incremental mode. Notice this method may modify
   * the options to ensure that we are compatible with incremental mode.
   *
   * If this method returns true, then the reason why we were incompatible with
   * incremental mode is written on the reason output stream. Suggestions for how to
   * resolve the incompatibility exception are written on the suggest stream.
   */
  bool incompatibleWithIncremental(const LogicInfo& logic,
                                   Options& opts,
                                   std::ostream& reason,
                                   std::ostream& suggest) const;
  /**
   * Return true if proofs must be disabled. This is the case for any technique
   * that answers "unsat" without showing a proof of unsatisfiabilty. The output
   * stream reason is similar to above.
   */
  bool incompatibleWithProofs(const Options& opts, std::ostream& reason) const;
  /**
   * Check whether we should disable models. The output stream reason is similar
   * to above.
   */
  bool incompatibleWithModels(const Options& opts, std::ostream& reason) const;
  /**
   * Check if incompatible with unsat cores. Notice this method may modify
   * the options to ensure that we are compatible with unsat cores.
   * The output stream reason is similar to above.
   */
  bool incompatibleWithUnsatCores(Options& opts, std::ostream& reason) const;
  /**
   * Return true if we are using "safe" unsat cores, which disables all
   * techniques that may interfere with producing correct unsat cores.
   */
  bool safeUnsatCores(const Options& opts) const;
  //------------------------- options setting, prior finalization of logic
  /**
   * Set defaults pre, which sets all options prior to finalizing the logic.
   * It is required that any options that impact the finalization of logic
   * (finalizeLogic).
   */
  void setDefaultsPre(Options& opts);
  //------------------------- finalization of the logic
  /**
   * Finalize the logic based on the options.
   */
  void finalizeLogic(LogicInfo& logic, Options& opts) const;
  /**
   * Widen logic to theories that are required, since some theories imply the
   * use of other theories to handle certain operators, e.g. UF to handle
   * partial functions.
   */
  void widenLogic(LogicInfo& logic, Options& opts) const;
  //------------------------- options setting, post finalization of logic
  /**
   * Set all default options, after we have finalized the logic.
   */
  void setDefaultsPost(const LogicInfo& logic, Options& opts) const;
  /**
   * Set defaults related to quantifiers, called when quantifiers are enabled.
   * This method modifies opt.quantifiers only.
   */
  void setDefaultsQuantifiers(const LogicInfo& logic, Options& opts) const;
  /**
   * Set defaults related to SyGuS, called when SyGuS is enabled.
   */
  void setDefaultsSygus(Options& opts) const;
  /**
   * Set default decision mode
   */
  void setDefaultDecisionMode(const LogicInfo& logic, Options& opts) const;
  /** Are we an internal subsolver? */
  bool d_isInternalSubsolver;
};

}  // namespace smt
}  // namespace cvc5

#endif /* CVC5__SMT__SET_DEFAULTS_H */
