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
  /**
   * Determine whether we will be solving a SyGuS problem.
   */
  bool isSygus(const Options& opts) const;
  /**
   * Determine whether we will be using SyGuS.
   */
  bool usesSygus(const Options& opts) const;
  /**
   * Return true if proofs must be disabled. This is the case for any technique
   * that answers "unsat" without showing a proof of unsatisfiabilty.
   */
  bool mustDisableProofs(const Options& opts) const;
  /**
   * Widen logic to theories that are required, since some theories imply the
   * use of other theories to handle certain operators, e.g. UF to handle
   * partial functions.
   */
  void widenLogic(LogicInfo& logic, Options& opts) const;
  /**
   * Set defaults related to quantifiers, called when quantifiers are enabled.
   * This method modifies opt.quantifiers only.
   */
  void setDefaultsQuantifiers(const LogicInfo& logic,
                              Options& opts) const;
  /**
   * Set defaults related to SyGuS, called when SyGuS is enabled.
   */
  void setDefaultsSygus(Options& opts) const;
  /**
   * Set default decision mode
   */
  void setDefaultDecisionMode(const LogicInfo& logic,
                              Options& opts) const;
  /** Are we an internal subsolver? */
  bool d_isInternalSubsolver;
};

}  // namespace smt
}  // namespace cvc5

#endif /* CVC5__SMT__SET_DEFAULTS_H */
