/******************************************************************************
 * Top contributors (to current version):
 *   Ying Sheng, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The solver for interpolation queries.
 */

#include "smt/interpolation_solver.h"

#include <sstream>

#include "base/modal_exception.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "smt/env.h"
#include "smt/set_defaults.h"
#include "smt/sygus_solver.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/sygus/sygus_interpol.h"
#include "theory/smt_engine_subsolver.h"
#include "theory/trust_substitutions.h"

using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace smt {

InterpolationSolver::InterpolationSolver(Env& env) : EnvObj(env) {}

InterpolationSolver::~InterpolationSolver() {}

bool InterpolationSolver::getInterpolant(const std::vector<Node>& axioms,
                                         const Node& conj,
                                         const TypeNode& grammarType,
                                         Node& interpol)
{
  if (!options().smt.produceInterpolants)
  {
    const char* msg =
        "Cannot get interpolation when produce-interpolants options is off.";
    throw ModalException(msg);
  }
  Trace("sygus-interpol") << "SolverEngine::getInterpol: conjecture " << conj
                          << std::endl;
  // must expand definitions
  Node conjn = d_env.getTopLevelSubstitutions().apply(conj);
  conjn = rewrite(conjn);
  std::string name("__internal_interpol");

  d_subsolver = std::make_unique<quantifiers::SygusInterpol>(d_env);
  if (d_subsolver->solveInterpolation(
          name, axioms, conjn, grammarType, interpol))
  {
    if (options().smt.checkInterpolants)
    {
      checkInterpol(interpol, axioms, conj);
    }
    return true;
  }
  return false;
}

bool InterpolationSolver::getInterpolantNext(Node& interpol)
{
  // should already have initialized a subsolver, since we are immediately
  // preceeded by a successful call to get-interpolant(-next).
  Assert(d_subsolver != nullptr);
  return d_subsolver->solveInterpolationNext(interpol);
}

void InterpolationSolver::checkInterpol(Node interpol,
                                        const std::vector<Node>& easserts,
                                        const Node& conj)
{
  Assert(interpol.getType().isBoolean());
  Trace("check-interpol")
      << "SolverEngine::checkInterpol: get expanded assertions" << std::endl;
  bool canTrustResult = SygusSolver::canTrustSynthesisResult(options());
  if (!canTrustResult)
  {
    warning() << "Running check-interpolants is not guaranteed to pass with "
                 "the current options."
              << std::endl;
  }

  Options subOptions;
  subOptions.copyValues(d_env.getOptions());
  subOptions.writeSmt().produceInterpolants = false;
  SetDefaults::disableChecking(subOptions);
  SubsolverSetupInfo ssi(d_env, subOptions);
  // two checks: first, axioms imply interpol, second, interpol implies conj.
  for (unsigned j = 0; j < 2; j++)
  {
    if (j == 1)
    {
      Trace("check-interpol")
          << "SolverEngine::checkInterpol: conjecture is " << conj << std::endl;
    }
    Trace("check-interpol") << "SolverEngine::checkInterpol: phase " << j
                            << ": make new SMT engine" << std::endl;
    // Start new SMT engine to check solution
    std::unique_ptr<SolverEngine> itpChecker;
    initializeSubsolver(itpChecker, ssi);
    Trace("check-interpol") << "SolverEngine::checkInterpol: phase " << j
                            << ": asserting formulas" << std::endl;
    if (j == 0)
    {
      for (const Node& e : easserts)
      {
        itpChecker->assertFormula(e);
      }
      Node negitp = interpol.notNode();
      itpChecker->assertFormula(negitp);
    }
    else
    {
      itpChecker->assertFormula(interpol);
      Assert(!conj.isNull());
      itpChecker->assertFormula(conj.notNode());
    }
    Trace("check-interpol") << "SolverEngine::checkInterpol: phase " << j
                            << ": check the assertions" << std::endl;
    Result r = itpChecker->checkSat();
    Trace("check-interpol") << "SolverEngine::checkInterpol: phase " << j
                            << ": result is " << r << std::endl;
    std::stringstream serr;
    if (r.getStatus() != Result::UNSAT)
    {
      if (j == 0)
      {
        serr << "SolverEngine::checkInterpol(): negated produced solution "
                "cannot be shown "
                "satisfiable with assertions, result was "
             << r;
      }
      else
      {
        serr << "SolverEngine::checkInterpol(): negated conjecture cannot be "
                "shown satisfiable with produced solution, result was "
             << r;
      }
      bool hardFailure = canTrustResult && !r.isUnknown();
      if (hardFailure)
      {
        InternalError() << serr.str();
      }
      else
      {
        warning() << serr.str() << std::endl;
      }
    }
  }
}

}  // namespace smt
}  // namespace cvc5::internal
