/*********************                                                        */
/*! \file model_core_builder.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of utility for building model cores
 **/

#include "smt/model_core_builder.h"

#include "theory/subs_minimize.h"

using namespace CVC4::kind;

namespace CVC4 {

bool ModelCoreBuilder::setModelCore(const std::vector<Expr>& assertions,
                                    Model* m,
                                    options::ModelCoresMode mode)
{
  if (Trace.isOn("model-core"))
  {
    Trace("model-core") << "Compute model core, assertions:" << std::endl;
    for (const Node& a : assertions)
    {
      Trace("model-core") << "  " << a << std::endl;
    }
  }

  // convert to nodes
  std::vector<Node> asserts;
  for (unsigned i = 0, size = assertions.size(); i < size; i++)
  {
    asserts.push_back(Node::fromExpr(assertions[i]));
  }
  NodeManager* nm = NodeManager::currentNM();

  Node formula = asserts.size() > 1? nm->mkNode(AND, asserts) : asserts[0];
  std::vector<Node> vars;
  std::vector<Node> subs;
  Trace("model-core") << "Assignments: " << std::endl;
  std::unordered_set<TNode, TNodeHashFunction> visited;
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
        Node vcur = Node::fromExpr(m->getValue(cur.toExpr()));
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
  bool minimized = false;
  if (mode == options::ModelCoresMode::NON_IMPLIED)
  {
    minimized = theory::SubstitutionMinimize::findWithImplied(
        formula, vars, subs, coreVars, impliedVars);
  }
  else if (mode == options::ModelCoresMode::SIMPLE)
  {
    minimized = theory::SubstitutionMinimize::find(
        formula, truen, vars, subs, coreVars);
  }
  else
  {
    Unreachable() << "Unknown model cores mode";
  }
  Assert(minimized)
      << "cannot compute model core, since model does not satisfy input!";
  if (minimized)
  {
    m->setUsingModelCore();
    Trace("model-core") << "...got core vars : " << coreVars << std::endl;

    for (const Node& cv : coreVars)
    {
      m->recordModelCoreSymbol(cv.toExpr());
    }
    return true;
  }
  Trace("model-core") << "...failed, model does not satisfy input!"
                      << std::endl;
  return false;
}

} /* namespace CVC4 */
