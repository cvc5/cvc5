/*********************                                                        */
/*! \file preprocessing_pass_context.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Justin Xu, Aina Niemetz, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
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

#include "context/context.h"
#include "decision/decision_engine.h"
#include "smt/smt_engine.h"
#include "theory/theory_engine.h"
#include "util/resource_manager.h"

namespace CVC4 {
namespace preprocessing {

class PreprocessingPassContext
{
 public:
  PreprocessingPassContext(SmtEngine* smt, ResourceManager* resourceManager);
  SmtEngine* getSmt() { return d_smt; }
  TheoryEngine* getTheoryEngine() { return d_smt->d_theoryEngine; }
  DecisionEngine* getDecisionEngine() { return d_smt->d_decisionEngine; }
  prop::PropEngine* getPropEngine() { return d_smt->d_propEngine; }
  context::Context* getUserContext() { return d_smt->d_userContext; }
  void spendResource(unsigned amount)
  {
    d_resourceManager->spendResource(amount);
  }

  /* Widen the logic to include the given theory. */
  void widenLogic(theory::TheoryId id);

 private:
  /* Pointer to the SmtEngine that this context was created in. */
  SmtEngine* d_smt;
  ResourceManager* d_resourceManager;
};  // class PreprocessingPassContext

}  // namespace preprocessing
}  // namespace CVC4

#endif /* __CVC4__PREPROCESSING__PREPROCESSING_PASS_CONTEXT_H */
