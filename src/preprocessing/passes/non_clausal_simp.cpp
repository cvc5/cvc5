/*********************                                                        */
/*! \file non_clausal_simp.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Non-clausal simplification preprocessing pass.
 **
 ** Run the nonclausal solver and try to solve all assigned theory literals.
 **/

#include "preprocessing/passes/non_clausal_simp.h"

#include "prop/registrar.h"
#include "prop/cnf_stream.h"
#include "prop/sat_solver_factory.h"

#include "proof/proof_manager.h"

#include "context/cdo.h"
#include "options/proof_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/theory_model.h"

#include <vector>

using namespace CVC4;
using namespace CVC4::theory;

namespace CVC4 {
namespace preprocessing {
namespace passes {


/* -------------------------------------------------------------------------- */

NonClausalSimp::NonClausalSimp(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "non-clausal-simp")
{
  d_satSolver = SatSolverFactory::createCryptoMinisat(smtStatisticsRegistry(), "non_clausal_simp_solver");

}

PreprocessingPassResult NonClausalSimp::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  Assert(!options::unsatCores() && !options::fewerPreprocessingHoles());

  d_preprocContext->spendResource(options::preprocessStep());

  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Trace("non-clausal-simplify") << "Assertion #" << i << " : "
                                  << (*assertionsToPreprocess)[i] << std::endl;
  }

  d_preprocContext->spendResource(options::preprocessStep());


  //SatSolver* d_satSolver = prop::SatSolverFactory::createCadical(smtStatisticsRegistry(),
                                                 //"non-clausal-simp");
  //Registrar d_registrar = new CVC4::prop::NullRegistrar();
  CVC4::prop::NullRegistrar d_registrar;
  //context::Context* d_context = new context::Context();
  context::Context d_context;
  //CnfStream* d_cnfStream = new
  CVC4::prop::TseitinCnfStream d_cnfStream (d_satSolver, &d_registrar, &d_context, true);


  Trace("non-clausal-simplify") << "asserting to sat solver" << std::endl;

  for (size_t i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    d_cnfStream.convertAndAssert((*assertionsToPreprocess)[i], false, false, RULE_GIVEN);

  }

  SatValue result = d_satSolver->solve();

  if (result==SAT_VALUE_FALSE) return PreprocessingPassResult::CONFLICT;

  return PreprocessingPassResult::NO_CONFLICT;

}  // namespace passes

/* -------------------------------------------------------------------------- */

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
