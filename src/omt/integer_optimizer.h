/*********************                                                        */
/*! \file integer_optimizer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Yancheng Ou
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Optimizer for Integer type
 **/

#ifndef CVC4__OMT__INTEGER_OPTIMIZER_H
#define CVC4__OMT__INTEGER_OPTIMIZER_H

#include "omt_optimizer.h"

namespace CVC4::smt {

/**
 * Optimizer for Integer type
 */
class OMTOptimizerInteger : public OMTOptimizer
{
 public:
  OMTOptimizerInteger() = default;
  virtual ~OMTOptimizerInteger() = default;
  virtual std::pair<OptResult, Node> minimize(SmtEngine* parentSMTSolver,
                                              Node target) override;
  virtual std::pair<OptResult, Node> maximize(SmtEngine* parentSMTSolver,
                                              Node target) override;

 private:
  /** Creates an SMT subsolver for offline optimization purpose **/
  std::unique_ptr<SmtEngine> createOptChecker(SmtEngine* parentSMTSolver);

  /**
   * Handles the optimization query specified by objType
   * (objType = OBJECTIVE_MINIMIZE / OBJECTIVE_MAXIMIZE)
   **/
  std::pair<OptResult, Node> optimize(SmtEngine* parentSMTSolver,
                                      Node target,
                                      ObjectiveType objType);
};

} // namespace CVC4::smt

#endif /* CVC4__OMT__INTEGER_OPTIMIZER_H */
