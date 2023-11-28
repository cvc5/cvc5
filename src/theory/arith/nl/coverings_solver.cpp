/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of new non-linear solver.
 */

#include "theory/arith/nl/coverings_solver.h"

#include "expr/skolem_manager.h"
#include "options/arith_options.h"
#include "smt/env.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/coverings/cdcac.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/arith/nl/poly_conversion.h"
#include "theory/inference_id.h"
#include "theory/theory.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

CoveringsSolver::CoveringsSolver(Env& env, InferenceManager& im, NlModel& model)
    :
      EnvObj(env),
#ifdef CVC5_POLY_IMP
      d_CAC(env),
#endif
      d_foundSatisfiability(false),
      d_im(im),
      d_model(model),
      d_eqsubs(env)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  d_ranVariable = sm->mkDummySkolem("__z", nm->realType(), "");
}

CoveringsSolver::~CoveringsSolver() {}

void CoveringsSolver::initLastCall(const std::vector<Node>& assertions)
{
#ifdef CVC5_POLY_IMP
  if (TraceIsOn("nl-cov"))
  {
    Trace("nl-cov") << "CoveringsSolver::initLastCall" << std::endl;
    Trace("nl-cov") << "* Assertions: " << std::endl;
    for (const Node& a : assertions)
    {
      Trace("nl-cov") << "  " << a << std::endl;
    }
  }
  if (options().arith.nlCovVarElim)
  {
    d_eqsubs.reset();
    std::vector<Node> processed = d_eqsubs.eliminateEqualities(assertions);
    if (d_eqsubs.hasConflict())
    {
        Node lem = NodeManager::currentNM()->mkAnd(d_eqsubs.getConflict()).negate();
        d_im.addPendingLemma(lem, InferenceId::ARITH_NL_COVERING_CONFLICT, nullptr);
        Trace("nl-cov") << "Found conflict: " << lem << std::endl;
        return;
    }
    if (TraceIsOn("nl-cov"))
    {
      Trace("nl-cov") << "After simplifications" << std::endl;
      Trace("nl-cov") << "* Assertions: " << std::endl;
      for (const Node& a : processed)
      {
        Trace("nl-cov") << "  " << a << std::endl;
      }
    }
    d_CAC.reset();
    for (const Node& a : processed)
    {
      Assert(!a.isConst());
      d_CAC.getConstraints().addConstraint(a);
    }
  }
  else
  {
    d_CAC.reset();
    for (const Node& a : assertions)
    {
      Assert(!a.isConst());
      d_CAC.getConstraints().addConstraint(a);
    }
  }
  d_CAC.computeVariableOrdering();
  d_CAC.retrieveInitialAssignment(d_model, d_ranVariable);
#else
  warning() << "Tried to use CoveringsSolver but libpoly is not available. Compile "
               "with --poly."
            << std::endl;
#endif
}

void CoveringsSolver::checkFull()
{
#ifdef CVC5_POLY_IMP
  if (d_CAC.getConstraints().getConstraints().empty()) {
    d_foundSatisfiability = true;
    Trace("nl-cov") << "No constraints. Return." << std::endl;
    return;
  }
  d_CAC.startNewProof();
  auto covering = d_CAC.getUnsatCover();
  if (covering.empty())
  {
    d_foundSatisfiability = true;
    Trace("nl-cov") << "SAT: " << d_CAC.getModel() << std::endl;
  }
  else
  {
    d_foundSatisfiability = false;
    auto mis = collectConstraints(covering);
    Trace("nl-cov") << "Collected MIS: " << mis << std::endl;
    Assert(!mis.empty()) << "Infeasible subset can not be empty";
    Trace("nl-cov") << "UNSAT with MIS: " << mis << std::endl;
    d_eqsubs.postprocessConflict(mis);
    Trace("nl-cov") << "After postprocessing: " << mis << std::endl;
    Node lem = NodeManager::currentNM()->mkAnd(mis).notNode();
    ProofGenerator* proof = d_CAC.closeProof(mis);
    d_im.addPendingLemma(lem, InferenceId::ARITH_NL_COVERING_CONFLICT, proof);
  }
#else
  warning() << "Tried to use CoveringsSolver but libpoly is not available. Compile "
               "with --poly."
            << std::endl;
#endif
}

void CoveringsSolver::checkPartial()
{
#ifdef CVC5_POLY_IMP
  if (d_CAC.getConstraints().getConstraints().empty()) {
    Trace("nl-cov") << "No constraints. Return." << std::endl;
    return;
  }
  auto covering = d_CAC.getUnsatCover(true);
  if (covering.empty())
  {
    d_foundSatisfiability = true;
    Trace("nl-cov") << "SAT: " << d_CAC.getModel() << std::endl;
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
        Trace("nl-cov") << "Excluding " << first_var << " -> "
                        << interval.d_interval << " using " << lemma
                        << std::endl;
        d_im.addPendingLemma(lemma,
                             InferenceId::ARITH_NL_COVERING_EXCLUDED_INTERVAL);
      }
    }
  }
#else
  warning() << "Tried to use CoveringsSolver but libpoly is not available. Compile "
               "with --poly."
            << std::endl;
#endif
}

bool CoveringsSolver::constructModelIfAvailable(std::vector<Node>& assertions)
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
    if (!Theory::isLeafOf(variable, TheoryId::THEORY_ARITH))
    {
      Trace("nl-cov") << "Not a variable: " << variable << std::endl;
      foundNonVariable = true;
    }
    Node value = value_to_node(d_CAC.getModel().get(v), variable);
    addToModel(variable, value);
  }
  for (const auto& sub : d_eqsubs.getSubstitutions())
  {
    Trace("nl-cov") << "EqSubs: " << sub.first << " -> " << sub.second
                    << std::endl;
    addToModel(sub.first, sub.second);
  }
  if (foundNonVariable)
  {
    Trace("nl-cov")
        << "Some variable was an extended term, don't clear list of assertions."
        << std::endl;
    return false;
  }
  Trace("nl-cov") << "Constructed a full assignment, clear list of assertions."
                  << std::endl;
  assertions.clear();
  return true;
#else
  warning() << "Tried to use CoveringsSolver but libpoly is not available. Compile "
               "with --poly."
            << std::endl;
  return false;
#endif
}

void CoveringsSolver::addToModel(TNode var, TNode value) const
{
  Assert(value.getType().isRealOrInt());
  // we must take its substituted form here, since other solvers (e.g. the
  // reductions inference of the sine solver) may have introduced substitutions
  // internally during check.
  Node svalue = d_model.getSubstitutedForm(value);
  // ensure the value has integer type if var has integer type
  if (var.getType().isInteger())
  {
    if (svalue.getKind() == Kind::TO_REAL)
    {
      svalue = svalue[0];
    }
    else if (svalue.getKind() == Kind::CONST_RATIONAL)
    {
      Assert(svalue.getConst<Rational>().isIntegral());
      svalue =
          NodeManager::currentNM()->mkConstInt(svalue.getConst<Rational>());
    }
  }
  Trace("nl-cov") << "-> " << var << " = " << svalue << std::endl;
  d_model.addSubstitution(var, svalue);
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
