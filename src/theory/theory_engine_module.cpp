/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Virtual class for theory engine modules
 */

#include "theory/theory_engine_module.h"

namespace cvc5::internal {
namespace theory {

  TheoryEngineModule::TheoryEngineModule(Env& env) : EnvObj(env){}
  void TheoryEngineModule::check(Theory::Effort effort){}
  void TheoryEngineModule::postCheck(Theory::Effort effort){}
  void TheoryEngineModule::notifyLemma(TNode n){}
  void TheoryEngineModule::notifyCandidateModel(TheoryModel* m){}


}  // namespace theory
}  // namespace cvc5::internal
