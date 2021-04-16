/******************************************************************************
 * Top contributors (to current version):
 *   Liana Hadarean, Alex Ozdemir, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The interface for things that want to recieve notification from the SAT
 * solver.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__BVSATSOLVERNOTIFY_H
#define CVC5__PROP__BVSATSOLVERNOTIFY_H

#include "prop/sat_solver_types.h"
#include "util/resource_manager.h"

namespace cvc5 {
namespace prop {

class BVSatSolverNotify {
public:

  virtual ~BVSatSolverNotify() {};

  /**
   * If the notify returns false, the solver will break out of whatever it's currently doing
   * with an "unknown" answer.
   */
  virtual bool notify(SatLiteral lit) = 0;

  /**
   * Notify about a learnt clause.
   */
  virtual void notify(SatClause& clause) = 0;
  virtual void spendResource(Resource r) = 0;
  virtual void safePoint(Resource r) = 0;

};/* class BVSatSolverInterface::Notify */

}
}  // namespace cvc5

#endif
