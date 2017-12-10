/*********************                                                        */
/*! \file preprocessing_pass_context.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The preprocessing pass context for passes
 **
 ** Implementation of the preprocessing pass context for passes. This context
 ** allows preprocessing passes to retrieve information besides the assertions
 ** from the solver and interact with it without getting full access.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PREPROCESSING__PREPROCESSING_PASS_CONTEXT_H
#define __CVC4__PREPROCESSING__PREPROCESSING_PASS_CONTEXT_H

#include "decision/decision_engine.h"
#include "smt/smt_engine.h"
#include "theory/arith/pseudoboolean_proc.h"
#include "theory/booleans/circuit_propagator.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace preprocessing {

class PreprocessingPassContext {
 public:
  PreprocessingPassContext(SmtEngine* smt);
  SmtEngine* getSmt() { return d_smt; }
  TheoryEngine* getTheoryEngine() { return d_smt->d_theoryEngine; }
  DecisionEngine* getDecisionEngine() { return d_smt->d_decisionEngine; }
  prop::PropEngine* getPropEngine() { return d_smt->d_propEngine; }

 private:
  /* Pointer to the SmtEngine that this context was created in. */
  SmtEngine* d_smt;
};  // class PreprocessingPassContext

}  // namespace preprocessing
}  // namespace CVC4

#endif /* __CVC4__PREPROCESSING__PREPROCESSING_PASS_CONTEXT_H */
