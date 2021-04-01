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

#include "omt/omt_optimizer.h"

namespace cvc5::omt {

/**
 * Optimizer for Integer type
 */
class OMTOptimizerInteger : public OMTOptimizer
{
 public:
  OMTOptimizerInteger() = default;
  virtual ~OMTOptimizerInteger() = default;
  std::pair<smt::OptResult, Node> minimize(SmtEngine* parentSMTSolver,
                                           Node target) override;
  std::pair<smt::OptResult, Node> maximize(SmtEngine* parentSMTSolver,
                                           Node target) override;

 private:
  /**
   * Handles the optimization query specified by objType
   * (objType = OBJECTIVE_MINIMIZE / OBJECTIVE_MAXIMIZE)
   **/
  std::pair<smt::OptResult, Node> optimize(SmtEngine* parentSMTSolver,
                                           Node target,
                                           smt::ObjectiveType objType);
};

}  // namespace cvc5::omt

#endif /* CVC4__OMT__INTEGER_OPTIMIZER_H */
