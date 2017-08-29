/*********************                                                        */
/*! \file preprocessing_pass_api.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Preprocessing pass API for passes
 **
 ** The preprocessing pass API is the interface between solver and
 ** preprocessing passes. Passes are expected to use API for 
 ** read only access.
 **/
#include "cvc4_private.h"

#ifndef __CVC4__PREPROC__PREPROCESSING_PASS_CONTEXT_H
#define __CVC4__PREPROC__PREPROCESSING_PASS_CONTEXT_H

#include <string>
#include "decision/decision_engine.h"
#include "smt/smt_engine.h"
#include "theory/arith/pseudoboolean_proc.h"
#include "theory/booleans/circuit_propagator.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace preproc {

class PreprocessingPassContext {
 public:
  PreprocessingPassContext(SmtEngine* smt);
  SmtEngine* getSmt() { return d_smt; }
  TheoryEngine* getTheoryEngine() { return d_smt->d_theoryEngine; }
  DecisionEngine* getDecisionEngine() { return d_smt->d_decisionEngine; }
  prop::PropEngine* getPropEngine() { return d_smt->d_propEngine; }

 private:
  /* SmtEngine that is used to get variables */
  SmtEngine* d_smt;
};  // class PreprocessingPassContext

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC__PREPROCESSING_PASS_CONTEXT_H */
