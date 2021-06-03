/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of new non-linear solver.
 */

#include "theory/arith/nl/cad_solver.h"

#include "expr/skolem_manager.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/cad/cdcac.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/arith/nl/poly_conversion.h"
#include "theory/inference_id.h"

namespace cvc5 {
namespace theory {
namespace arith {
namespace nl {

CadSolver::CadSolver(InferenceManager& im,
                     NlModel& model,
                     context::Context* ctx,
                     ProofNodeManager* pnm)
    :
#ifdef CVC5_POLY_IMP
      d_CAC(ctx, pnm),
#endif
      d_foundSatisfiability(false),
      d_im(im),
      d_model(model)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  d_ranVariable = sm->mkDummySkolem(
      "__z", nm->realType(), "", NodeManager::SKOLEM_EXACT_NAME);
#ifdef CVC5_POLY_IMP
  ProofChecker* pc = pnm != nullptr ? pnm->getChecker() : nullptr;
  if (pc != nullptr)
  {
    // add checkers
    d_proofChecker.registerTo(pc);
  }
#endif
}

CadSolver::~CadSolver() {}

void CadSolver::initLastCall(const std::vector<Node>& assertions)
{
#ifdef CVC5_POLY_IMP
  if (Trace.isOn("nl-cad"))
  {
    Trace("nl-cad") << "CadSolver::initLastCall" << std::endl;
    Trace("nl-cad") << "* Assertions: " << std::endl;
    for (const Node& a : assertions)
    {
      Trace("nl-cad") << "  " << a << std::endl;
    }
  }
  // store or process assertions
  d_CAC.reset();
  for (const Node& a : assertions)
  {
    d_CAC.getConstraints().addConstraint(a);
  }
  d_CAC.computeVariableOrdering();
  d_CAC.retrieveInitialAssignment(d_model, d_ranVariable);
#else
  Warning() << "Tried to use CadSolver but libpoly is not available. Compile "
               "with --poly."
            << std::endl;
#endif
}

void CadSolver::checkFull()
{
#ifdef CVC5_POLY_IMP
  if (d_CAC.getConstraints().getConstraints().empty()) {
    Trace("nl-cad") << "No constraints. Return." << std::endl;
    return;
  }
  d_CAC.startNewProof();
  auto covering = d_CAC.getUnsatCover();
  if (covering.empty())
  {
    d_foundSatisfiability = true;
    Trace("nl-cad") << "SAT: " << d_CAC.getModel() << std::endl;
  }
  else
  {
    d_foundSatisfiability = false;
    auto mis = collectConstraints(covering);
    Trace("nl-cad") << "Collected MIS: " << mis << std::endl;
    Assert(!mis.empty()) << "Infeasible subset can not be empty";
    Trace("nl-cad") << "UNSAT with MIS: " << mis << std::endl;
    Node lem = NodeManager::currentNM()->mkAnd(mis).negate();
    ProofGenerator* proof = d_CAC.closeProof(mis);
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_CAD_CONFLICT, proof);
  }
#else
  Warning() << "Tried to use CadSolver but libpoly is not available. Compile "
               "with --poly."
            << std::endl;
#endif
}

void CadSolver::checkPartial()
{
#ifdef CVC5_POLY_IMP
  if (d_CAC.getConstraints().getConstraints().empty()) {
    Trace("nl-cad") << "No constraints. Return." << std::endl;
    return;
  }
  auto covering = d_CAC.getUnsatCover(0, true);
  if (covering.empty())
  {
    d_foundSatisfiability = true;
    Trace("nl-cad") << "SAT: " << d_CAC.getModel() << std::endl;
  }
  else
  {
    auto* nm = NodeManager::currentNM();
    Node first_var =
        d_CAC.getConstraints().varMapper()(d_CAC.getVariableOrdering()[0]);
    for (const auto& interval : covering)
    {
      Node premise;
      Assert(!interval.d_origins.empty());
      if (interval.d_origins.size() == 1)
      {
        premise = interval.d_origins[0];
      }
      else
      {
        premise = nm->mkNode(Kind::AND, interval.d_origins);
      }
      Node conclusion =
          excluding_interval_to_lemma(first_var, interval.d_interval, false);
      if (!conclusion.isNull())
      {
        Node lemma = nm->mkNode(Kind::IMPLIES, premise, conclusion);
        Trace("nl-cad") << "Excluding " << first_var << " -> "
                        << interval.d_interval << " using " << lemma
                        << std::endl;
        d_im.addPendingLemma(lemma,
                             InferenceId::ARITH_NL_CAD_EXCLUDED_INTERVAL);
      }
    }
  }
#else
  Warning() << "Tried to use CadSolver but libpoly is not available. Compile "
               "with --poly."
            << std::endl;
#endif
}

bool CadSolver::constructModelIfAvailable(std::vector<Node>& assertions)
{
#ifdef CVC5_POLY_IMP
  if (!d_foundSatisfiability)
  {
    return false;
  }
  bool foundNonVariable = false;
  for (const auto& v : d_CAC.getVariableOrdering())
  {
    Node variable = d_CAC.getConstraints().varMapper()(v);
    if (!variable.isVar())
    {
      Trace("nl-cad") << "Not a variable: " << variable << std::endl;
      foundNonVariable = true;
    }
    Node value = value_to_node(d_CAC.getModel().get(v), d_ranVariable);
    if (value.isConst())
    {
      d_model.addCheckModelSubstitution(variable, value);
    }
    else
    {
      d_model.addCheckModelWitness(variable, value);
    }
    Trace("nl-cad") << "-> " << v << " = " << value << std::endl;
  }
  if (foundNonVariable)
  {
    Trace("nl-cad")
        << "Some variable was an extended term, don't clear list of assertions."
        << std::endl;
    return false;
  }
  Trace("nl-cad") << "Constructed a full assignment, clear list of assertions."
                  << std::endl;
  assertions.clear();
  return true;
#else
  Warning() << "Tried to use CadSolver but libpoly is not available. Compile "
               "with --poly."
            << std::endl;
  return false;
#endif
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5
