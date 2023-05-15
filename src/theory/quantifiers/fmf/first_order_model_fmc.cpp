/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of first order model for full model check.
 */

#include "theory/quantifiers/fmf/first_order_model_fmc.h"

#include "expr/attribute.h"
#include "expr/skolem_manager.h"
#include "theory/quantifiers/fmf/full_model_check.h"
#include "theory/rewriter.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace fmcheck {

/**
 * Marks that a term represents the entire domain of quantified formula for
 * the finite model finding fmc algorithm.
 */
struct IsStarAttributeId
{
};
using IsStarAttribute = expr::Attribute<IsStarAttributeId, bool>;

FirstOrderModelFmc::FirstOrderModelFmc(Env& env,
                                       QuantifiersState& qs,
                                       QuantifiersRegistry& qr,
                                       TermRegistry& tr)
    : FirstOrderModel(env, qs, qr, tr)
{
}

FirstOrderModelFmc::~FirstOrderModelFmc()
{
  for (std::pair<const Node, Def*>& d : d_models)
  {
    delete d.second;
  }
}

void FirstOrderModelFmc::processInitialize(bool ispre)
{
  if (!ispre)
  {
    return;
  }
  for (std::pair<const Node, Def*>& d : d_models)
  {
    d.second->reset();
  }
}

void FirstOrderModelFmc::processInitializeModelForTerm(Node n)
{
  if (n.getKind() == APPLY_UF)
  {
    // cannot be a bound variable
    Node op = n.getOperator();
    if (op.getKind() != BOUND_VARIABLE)
    {
      if (d_models.find(op) == d_models.end())
      {
        d_models[op] = new Def;
      }
    }
  }
}

bool FirstOrderModelFmc::isStar(Node n)
{
  return n.getAttribute(IsStarAttribute());
}

Node FirstOrderModelFmc::getStar(TypeNode tn)
{
  std::map<TypeNode, Node>::iterator it = d_type_star.find(tn);
  if (it != d_type_star.end())
  {
    return it->second;
  }
  SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
  Node st =
      sm->mkDummySkolem("star", tn, "skolem created for full-model checking");
  d_type_star[tn] = st;
  st.setAttribute(IsStarAttribute(), true);
  return st;
}

Node FirstOrderModelFmc::getFunctionValue(Node op, const char* argPrefix)
{
  Trace("fmc-model") << "Get function value for " << op << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  TypeNode type = op.getType();
  std::vector<Node> vars;
  for (size_t i = 0, nargs = type.getNumChildren() - 1; i < nargs; i++)
  {
    std::stringstream ss;
    ss << argPrefix << (i + 1);
    Node b = nm->mkBoundVar(ss.str(), type[i]);
    vars.push_back(b);
  }
  Node boundVarList = nm->mkNode(BOUND_VAR_LIST, vars);
  Node curr;
  Def* odef = d_models[op];
  for (size_t i = 0, ncond = odef->d_cond.size(); i < ncond; i++)
  {
    size_t ii = (ncond - 1) - i;
    Node v = odef->d_value[ii];
    Trace("fmc-model-func") << "Value is : " << v << std::endl;
    if (curr.isNull())
    {
      Trace("fmc-model-func") << "base : " << v << std::endl;
      curr = v;
    }
    else
    {
      // make the condition
      Node cond = odef->d_cond[ii];
      Trace("fmc-model-func") << "...cond : " << cond << std::endl;
      std::vector<Node> children;
      for (size_t j = 0, nchild = cond.getNumChildren(); j < nchild; j++)
      {
        TypeNode tn = vars[j].getType();
        if (!isStar(cond[j]))
        {
          Node c = getRepresentative(cond[j]);
          c = getRepresentative(c);
          children.push_back(nm->mkNode(EQUAL, vars[j], c));
        }
      }
      Assert(!children.empty());
      Node cc = nm->mkAnd(children);

      Trace("fmc-model-func")
          << "condition : " << cc << ", value : " << v << std::endl;
      curr = nm->mkNode(ITE, cc, v, curr);
    }
  }
  Trace("fmc-model") << "Made " << curr << " for " << op << std::endl;
  curr = rewrite(curr);
  return nm->mkNode(LAMBDA, boundVarList, curr);
}

}  // namespace fmcheck
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
