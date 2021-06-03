/******************************************************************************
 * Top contributors (to current version):
 *   Ying Sheng, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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
#include "options/smt_options.h"
#include "smt/env.h"
#include "smt/smt_engine.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"
#include "theory/quantifiers/sygus/sygus_interpol.h"
#include "theory/smt_engine_subsolver.h"
#include "theory/trust_substitutions.h"

using namespace cvc5::theory;

namespace cvc5 {
namespace smt {

InterpolationSolver::InterpolationSolver(SmtEngine* parent) : d_parent(parent)
{
}

InterpolationSolver::~InterpolationSolver() {}

bool InterpolationSolver::getInterpol(const Node& conj,
                                      const TypeNode& grammarType,
                                      Node& interpol)
{
  if (options::produceInterpols() == options::ProduceInterpols::NONE)
  {
    const char* msg =
        "Cannot get interpolation when produce-interpol options is off.";
    throw ModalException(msg);
  }
  Trace("sygus-interpol") << "SmtEngine::getInterpol: conjecture " << conj
                          << std::endl;
  std::vector<Node> axioms = d_parent->getExpandedAssertions();
  // must expand definitions
  Node conjn = d_parent->getEnv().getTopLevelSubstitutions().apply(conj);
  std::string name("A");

  quantifiers::SygusInterpol interpolSolver;
  if (interpolSolver.solveInterpolation(
          name, axioms, conjn, grammarType, interpol))
  {
    if (options::checkInterpols())
    {
      checkInterpol(interpol, axioms, conj);
    }
    return true;
  }
  return false;
}

bool InterpolationSolver::getInterpol(const Node& conj, Node& interpol)
{
  TypeNode grammarType;
  return getInterpol(conj, grammarType, interpol);
}

void InterpolationSolver::checkInterpol(Node interpol,
                                        const std::vector<Node>& easserts,
                                        const Node& conj)
{
  Assert(interpol.getType().isBoolean());
  Trace("check-interpol") << "SmtEngine::checkInterpol: get expanded assertions"
                          << std::endl;

  // two checks: first, axioms imply interpol, second, interpol implies conj.
  for (unsigned j = 0; j < 2; j++)
  {
    if (j == 1)
    {
      Trace("check-interpol")
          << "SmtEngine::checkInterpol: conjecture is " << conj << std::endl;
    }
    Trace("check-interpol") << "SmtEngine::checkInterpol: phase " << j
                            << ": make new SMT engine" << std::endl;
    // Start new SMT engine to check solution
    std::unique_ptr<SmtEngine> itpChecker;
    initializeSubsolver(itpChecker);
    Trace("check-interpol") << "SmtEngine::checkInterpol: phase " << j
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
    Trace("check-interpol") << "SmtEngine::checkInterpol: phase " << j
                            << ": check the assertions" << std::endl;
    Result r = itpChecker->checkSat();
    Trace("check-interpol") << "SmtEngine::checkInterpol: phase " << j
                            << ": result is " << r << std::endl;
    std::stringstream serr;
    if (r.asSatisfiabilityResult().isSat() != Result::UNSAT)
    {
      if (j == 0)
      {
        serr << "SmtEngine::checkInterpol(): negated produced solution cannot "
                "be shown "
                "satisfiable with assertions, result was "
             << r;
      }
      else
      {
        serr
            << "SmtEngine::checkInterpol(): negated conjecture cannot be shown "
               "satisfiable with produced solution, result was "
            << r;
      }
      InternalError() << serr.str();
    }
  }
}

}  // namespace smt
}  // namespace cvc5
