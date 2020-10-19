/*********************                                                        */
/*! \file check_models.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utility for checking models
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__CHECK_MODELS_H
#define CVC4__SMT__CHECK_MODELS_H

#include <unordered_map>

#include "context/context.h"
#include "expr/node.h"
#include "smt/model.h"
#include "smt/smt_solver.h"
#include "theory/substitutions.h"

namespace CVC4 {
namespace smt {

/**
 * This utility is responsible for checking the current model.
 */
class CheckModels
{
 public:
  CheckModels(SmtSolver& s);
  ~CheckModels();
  /**
   * Check model m against assertion list al.
   */
  void checkModel(Model* m, context::CDList<Node>* al);

 private:
  /** Reference to the SMT solver */
  SmtSolver& d_smt;
};

}  // namespace smt
}  // namespace CVC4

#endif
