/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of utility for building model cores.
 */

#include "smt/model_core_builder.h"

#include "theory/subs_minimize.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

ModelCoreBuilder::ModelCoreBuilder(Env& env) : EnvObj(env) {}

bool ModelCoreBuilder::setModelCore(const std::vector<Node>& assertions,
                                    theory::TheoryModel* m,
                                    options::ModelCoresMode mode)
{
  if (m->isUsingModelCore())
  {
    // already computed
    return true;
  }
  if (TraceIsOn("model-core"))
  {
    Trace("model-core") << "Compute model core, assertions:" << std::endl;
    for (const Node& a : assertions)
    {
      Trace("model-core") << "  " << a << std::endl;
    }
  }

  // convert to nodes
  NodeManager* nm = NodeManager::currentNM();

  Node formula = nm->mkAnd(assertions);
  std::vector<Node> vars;
  std::vector<Node> subs;
  Trace("model-core") << "Assignments: " << std::endl;
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(formula);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (cur.isVar())
      {
        Node vcur = m->getValue(cur);
        Trace("model-core") << "  " << cur << " -> " << vcur << std::endl;
        vars.push_back(cur);
        subs.push_back(vcur);
      }
      if (cur.getMetaKind() == metakind::PARAMETERIZED)
      {
        visit.push_back(cur.getOperator());
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());

  Node truen = nm->mkConst(true);

  Trace("model-core") << "Minimizing substitution..." << std::endl;
  std::vector<Node> coreVars;
  std::vector<Node> impliedVars;
  theory::SubstitutionMinimize sm(d_env);
  if (mode == options::ModelCoresMode::NON_IMPLIED)
  {
    sm.findWithImplied(formula, vars, subs, coreVars, impliedVars);
  }
  else if (mode == options::ModelCoresMode::SIMPLE)
  {
    sm.find(formula, truen, vars, subs, coreVars);
  }
  else
  {
    Unreachable() << "Unknown model cores mode";
  }
  m->setUsingModelCore();
  Trace("model-core") << "...got core vars : " << coreVars << std::endl;

  for (const Node& cv : coreVars)
  {
    m->recordModelCoreSymbol(cv);
  }
  return true;
}

}  // namespace cvc5::internal
