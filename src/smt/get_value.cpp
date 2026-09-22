/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for getting model values.
 */

#include "smt/get_value.h"

#include "expr/non_closed_node_converter.h"
#include "expr/skolem_manager.h"
#include "options/smt_options.h"
#include "prop/prop_engine.h"
#include "smt/env.h"
#include "smt/set_defaults.h"
#include "smt/smt_solver.h"
#include "theory/smt_engine_subsolver.h"
#include "theory/theory_model.h"
#include "theory/trust_substitutions.h"
#include "util/resource_manager.h"

using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace smt {

GetValue::GetValue(Env& env, SolverEngine& solver)
    : EnvObj(env), d_solver(solver), d_expDef(env)
{
}

Node GetValue::getValue(const Node& t, bool fromUser)
{
  TypeNode expectedType = t.getType();

  // We must expand definitions here, which replaces certain subterms of t
  // by the form that is used internally. This is necessary for some corner
  // cases of get-value to be accurate, e.g., when getting the value of
  // a division-by-zero term, we require getting the appropriate skolem
  // function corresponding to division-by-zero which may have been used during
  // the previous satisfiability check.
  //
  // Note that each of the three steps below (substitution, expand definitions,
  // rewriting) is cached by the utility that implements it, where each such
  // cache is invalidated when the state it depends on changes. In particular,
  // d_expDef maintains its cache for the lifetime of this solver engine, since
  // expanded forms do not depend on the current assertions. This makes
  // repeated calls to get-value on the same term (e.g. when enumerating
  // models) constant time in the size of that term.
  //
  // Must apply substitutions first to ensure we expand definitions in the
  // solved form of t as well.
  Node n = d_env.getTopLevelSubstitutions().apply(t);
  n = d_expDef.expandDefinitions(n);

  Trace("smt") << "--- getting value of " << n << std::endl;
  // There are two ways model values for terms are computed (for historical
  // reasons).  One way is that used in check-model; the other is that
  // used by the Model classes.  It's not clear to me exactly how these
  // two are different, but they need to be unified.  This ugly hack here
  // is to fix bug 554 until we can revamp boolean-terms and models [MGD]

  // AJR : necessary?
  if (!n.getType().isFunction())
  {
    n = rewrite(n);
  }

  // Fast path: if n is a Boolean term that the prop engine already has a SAT
  // literal for, and that literal has a value on the current SAT trail, then
  // that value is its value in the model. This is since the model is
  // constructed to satisfy the literals that were asserted to the theories,
  // which are those of the trail, and since the values of Boolean variables in
  // the model are read directly from the SAT solver, see
  // ModelManager::collectModelBooleanVariables.
  //
  // Taking this path means we do not build the theory model at all, which is
  // the main motivation for it: a caller that repeatedly checks satisfiability
  // and reads the values of literals of the input (e.g. to compute an
  // implicant or to add a blocking clause) never pays for model construction.
  //
  // We are conservative in the conditions under which we do this:
  // (1) We require SAT mode. In SAT_UNKNOWN mode the available model may have
  // been generated for a last call check, after which the SAT solver may have
  // backtracked, in which case the trail does not correspond to the model.
  // (2) We require that model cores are not being computed, since these are
  // computed as a side effect of getting the model in getAvailableModel.
  // (3) We do not call PropEngine::ensureLiteral, that is, we only take this
  // path for terms that already have a SAT literal. Getting a value should not
  // add literals or clauses to the SAT solver.
  // Note that we still check that a model is available, so that the exceptions
  // thrown by this method do not depend on which path is taken.
  bool bvalue;
  prop::PropEngine* pe = d_solver.d_smtSolver->getPropEngine();
  if (expectedType.isBoolean() && d_solver.getSmtMode() == SmtMode::SAT
      && options().smt.modelCoresMode == options::ModelCoresMode::NONE
      && pe->isSatLiteral(n) && pe->hasValue(n, bvalue))
  {
    d_solver.checkModelAvailable("get-value");
    Node bret = nodeManager()->mkConst(bvalue);
    Trace("smt") << "--- got value " << n << " = " << bret
                 << " (from SAT trail)" << std::endl;
    // Check that this agrees with the value the model would give. Note this
    // builds the model, hence we only do this when assertions are enabled.
    Assert(bret == d_solver.getAvailableModel("get-value")->getValue(n))
        << "Value of " << n << " on the SAT trail is " << bret
        << ", but its value in the model is "
        << d_solver.getAvailableModel("get-value")->getValue(n);
    return bret;
  }

  Trace("smt") << "--- getting value of " << n << std::endl;
  TheoryModel* m = d_solver.getAvailableModel("get-value");
  Assert(m != nullptr);
  Node resultNode = m->getValue(n);
  Trace("smt") << "--- got value " << n << " = " << resultNode << std::endl;
  Trace("smt") << "--- type " << resultNode.getType() << std::endl;
  Trace("smt") << "--- expected type " << expectedType << std::endl;

  // type-check the result we got
  Assert(resultNode.isNull() || resultNode.getType() == expectedType)
      << "Run with -t smt for details.";

  // Ensure it's a value (constant or const-ish like real algebraic
  // numbers), or a lambda (for uninterpreted functions). This assertion only
  // holds for models that do not have approximate values.
  if (!m->isValue(resultNode))
  {
    bool subSuccess = false;
    if (fromUser && options().smt.checkModelSubsolver)
    {
      // invoke satisfiability check
      // ensure symbols have been substituted
      resultNode = m->simplify(resultNode);
      // Note that we must be a "closed" term, i.e. one that can be
      // given in an assertion.
      if (NonClosedNodeConverter::isClosed(d_env, resultNode))
      {
        // set up a resource limit
        ResourceManager* rm = resourceManager();
        rm->beginCall();
        TypeNode rtn = resultNode.getType();
        SkolemManager* skm = nodeManager()->getSkolemManager();
        Node k = skm->mkInternalSkolemFunction(
            InternalSkolemId::GET_VALUE_PURIFY, rtn, {resultNode});
        // the query is (k = resultNode)
        Node checkQuery = resultNode.eqNode(k);
        Options subOptions;
        subOptions.copyValues(options());
        SetDefaults::disableChecking(subOptions);
        // ensure no infinite loop
        subOptions.write_smt().checkModelSubsolver = false;
        subOptions.write_smt().modelVarElimUneval = false;
        subOptions.write_smt().simplificationMode =
            options::SimplificationMode::NONE;
        // initialize the subsolver
        SubsolverSetupInfo ssi(d_env, subOptions);
        std::unique_ptr<SolverEngine> getValueChecker;
        initializeSubsolver(nodeManager(), getValueChecker, ssi);
        // disable all checking options
        SetDefaults::disableChecking(getValueChecker->getOptions());
        getValueChecker->assertFormula(checkQuery);
        Result r = getValueChecker->checkSat();
        if (r == Result::SAT)
        {
          // value is the result of getting the value of k
          resultNode = getValueChecker->getValue(k);
          subSuccess = m->isValue(resultNode);
        }
        // end resource limit
        rm->refresh();
      }
    }
    if (!subSuccess)
    {
      warning() << "Could not evaluate " << resultNode << " in getValue."
                << std::endl;
    }
  }

  if (options().smt.abstractValues)
  {
    TypeNode rtn = resultNode.getType();
    if (rtn.isArray())
    {
      // construct the skolem function
      SkolemManager* skm = nodeManager()->getSkolemManager();
      Node a = skm->mkInternalSkolemFunction(
          InternalSkolemId::ABSTRACT_VALUE, rtn, {resultNode});
      // add to top-level substitutions if applicable
      theory::TrustSubstitutionMap& tsm = d_env.getTopLevelSubstitutions();
      if (!tsm.get().hasSubstitution(resultNode))
      {
        tsm.addSubstitution(resultNode, a);
      }
      resultNode = a;
      Trace("smt") << "--- abstract value >> " << resultNode << std::endl;
    }
  }
  return resultNode;
}

}  // namespace smt
}  // namespace cvc5::internal
