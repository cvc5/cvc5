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
#include "smt/env.h"
#include "smt/expand_definitions.h"
#include "smt/set_defaults.h"
#include "theory/smt_engine_subsolver.h"
#include "theory/theory_model.h"
#include "theory/trust_substitutions.h"
#include "util/resource_manager.h"

using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace smt {

GetValue::GetValue(Env& env) : EnvObj(env) {}

Node GetValue::getValue(TheoryModel* m, const Node& t, bool fromUser)
{
  Assert(m != nullptr);
  TypeNode expectedType = t.getType();

  // We must expand definitions here, which replaces certain subterms of t
  // by the form that is used internally. This is necessary for some corner
  // cases of get-value to be accurate, e.g., when getting the value of
  // a division-by-zero term, we require getting the appropriate skolem
  // function corresponding to division-by-zero which may have been used during
  // the previous satisfiability check.
  std::unordered_map<Node, Node> cache;
  ExpandDefs expDef(d_env);
  // Must apply substitutions first to ensure we expand definitions in the
  // solved form of t as well.
  Node n = d_env.getTopLevelSubstitutions().apply(t);
  n = expDef.expandDefinitions(n, cache);

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

  Trace("smt") << "--- getting value of " << n << std::endl;
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
