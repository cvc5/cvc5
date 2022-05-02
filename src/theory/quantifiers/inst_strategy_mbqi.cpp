/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Model-based quantifier instantiation
 */

#include "theory/quantifiers/inst_strategy_mbqi.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "expr/subs.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/skolemize.h"
#include "theory/smt_engine_subsolver.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

InstStrategyMbqi::InstStrategyMbqi(Env& env,
                                   QuantifiersState& qs,
                                   QuantifiersInferenceManager& qim,
                                   QuantifiersRegistry& qr,
                                   TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr)
{
  // some kinds may appear in model values that cannot be asserted
  d_nonClosedKinds.insert(STORE_ALL);
  d_nonClosedKinds.insert(CODATATYPE_BOUND_VARIABLE);
}

void InstStrategyMbqi::reset_round(Theory::Effort e)
{
  d_quantChecked.clear();
  d_convertMap.clear();
}

bool InstStrategyMbqi::needsCheck(Theory::Effort e)
{
  return e >= Theory::EFFORT_LAST_CALL;
}

QuantifiersModule::QEffort InstStrategyMbqi::needsModel(Theory::Effort e)
{
  return QEFFORT_MODEL;
}

void InstStrategyMbqi::check(Theory::Effort e, QEffort quant_e)
{
  if (e != Theory::EFFORT_LAST_CALL || quant_e != QEFFORT_MODEL)
  {
    return;
  }
  Trace("mb-oracle") << "Run model-based oracle..." << std::endl;

  Trace("mb-oracle") << "  get the asserted quantified formulas...\n";
  // see if the negation of each quantified formula is satisfiable in the model
  std::vector<Node> disj;
  FirstOrderModel* fm = d_treg.getModel();
  std::vector<TNode> visit;
  for (size_t i = 0, nquant = fm->getNumAssertedQuantifiers(); i < nquant; i++)
  {
    Node q = fm->getAssertedQuantifier(i);
    Trace("mb-oracle-assert") << "  * " << q << std::endl;
    process(q);
  }
}

bool InstStrategyMbqi::checkCompleteFor(Node q)
{
  return d_quantChecked.find(q) != d_quantChecked.end();
}

void InstStrategyMbqi::process(Node q)
{
  // list of fresh variables per type
  std::map<TypeNode, std::unordered_set<Node> > freshVarType;
  // model values to the fresh variables
  std::map<Node, Node> mvToFreshVar;

  NodeManager* nm = NodeManager::currentNM();

  Skolemize* skm = d_qim.getSkolemize();
  Node body = skm->getSkolemizedBody(q);
  Node cbody = convert(body, true, d_convertMap, freshVarType, mvToFreshVar);

  // check if there are any bad kinds
  if (expr::hasSubtermKinds(d_nonClosedKinds, cbody))
  {
    return;
  }
  Assert(mvToFreshVar.empty());

  // get the skolem variables
  std::vector<Node> skolems;
  if (!skm->getSkolemConstants(q, skolems))
  {
    return;
  }

  std::vector<Node> constraints;

  // include the negation of the skolemized body
  constraints.push_back(cbody.negate());

  // also include distinctness of variables introduced as constants
  std::vector<Node> allVars;
  for (const std::pair<const TypeNode, std::unordered_set<Node> >& fv :
       freshVarType)
  {
    Assert(!fv.second.empty());
    allVars.insert(allVars.end(), fv.second.begin(), fv.second.end());
    if (fv.second.size() > 1)
    {
      std::vector<Node> vars(fv.second.begin(), fv.second.end());
      constraints.push_back(nm->mkNode(DISTINCT, vars));
    }
  }
  // TODO: ensure the skolems of the given type are equal to one of the
  // variables

  // make the query
  Node query = nm->mkAnd(constraints);

  std::unique_ptr<SolverEngine> mbqiChecker;
  initializeSubsolver(mbqiChecker, d_env);
  mbqiChecker->assertFormula(query);
  Trace("mb-oracle") << "*** Check sat..." << std::endl;
  Result r = mbqiChecker->checkSat();
  Trace("mb-oracle") << "  ...got : " << r << std::endl;
  if (r.getStatus() == Result::UNSAT)
  {
    d_quantChecked.insert(q);
    return;
  }

  // get the model values for all fresh variables
  Subs fvToInst;
  for (const Node& v : allVars)
  {
    Node mv = mbqiChecker->getValue(v);
    Assert(mvToFreshVar.find(mv) == mvToFreshVar.end());
    mvToFreshVar[mv] = v;
    // get a term that witnesses this variable
  }

  // get the model values for skolems
  std::vector<Node> mvs;
  getModelFromSubsolver(*mbqiChecker.get(), skolems, mvs);

  // try to convert those terms to an instantiation
  std::unordered_map<Node, Node> tmpConvertMap;
  for (Node& v : mvs)
  {
    v = convert(v, false, tmpConvertMap, freshVarType, mvToFreshVar);
    if (expr::hasSubtermKinds(d_nonClosedKinds, v))
    {
      return;
    }
    //
    v = fvToInst.apply(v);
  }

  // now convert fresh variables into terms
  for (Node& v : mvs)
  {
    v = fvToInst.apply(v);
  }

  // add instantiation?
}

Node InstStrategyMbqi::convert(
    Node t,
    bool toQuery,
    std::unordered_map<Node, Node>& cmap,
    std::map<TypeNode, std::unordered_set<Node> >& freshVarType,
    const std::map<Node, Node>& mvToFreshVar)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  FirstOrderModel* fm = d_treg.getModel();
  std::unordered_map<Node, Node>::iterator it;
  std::map<Node, Node> modelValue;
  std::unordered_set<Node> processingChildren;
  std::vector<TNode> visit;
  visit.push_back(t);
  TNode cur;
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = cmap.find(cur);
    if (it != cmap.end())
    {
      // already computed
      continue;
    }
    if (processingChildren.find(cur) == processingChildren.end())
    {
      Kind ck = cur.getKind();
      if (ck == BOUND_VARIABLE)
      {
        cmap[cur] = cur;
      }
      else if (ck == UNINTERPRETED_SORT_VALUE)
      {
        Assert(cur.getType().isUninterpretedSort());
        if (toQuery)
        {
          // return the fresh variable for this term
          Node k = sm->mkPurifySkolem(cur, "mbk");
          freshVarType[cur.getType()].insert(k);
          cmap[cur] = k;
          continue;
        }
        // converting from query, find the variable that it is equal to
        std::map<Node, Node>::const_iterator itmv = mvToFreshVar.find(cur);
        if (itmv != mvToFreshVar.end())
        {
          cmap[cur] = itmv->second;
        }
        else
        {
          // failed to find equal, keep the value
          cmap[cur] = cur;
        }
      }
      else if (cur.isVar())
      {
        std::map<Node, Node>::iterator itm = modelValue.find(cur);
        if (itm == modelValue.end())
        {
          Node mval = fm->getValue(cur);
          Trace("mb-oracle-model") << "  M[" << cur << "] = " << mval << "\n";
          modelValue[cur] = mval;
          visit.push_back(cur);
          visit.push_back(mval);
        }
        else
        {
          Assert(cmap.find(itm->second) != cmap.end());
          cmap[cur] = cmap[itm->second];
        }
      }
      else if (cur.getNumChildren() == 0)
      {
        cmap[cur] = cur;
      }
      else
      {
        processingChildren.insert(cur);
        visit.push_back(cur);
        if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
        {
          visit.push_back(cur.getOperator());
        }
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      continue;
    }
    processingChildren.erase(cur);
    bool childChanged = false;
    std::vector<Node> children;
    if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      children.push_back(cur.getOperator());
    }
    children.insert(children.end(), cur.begin(), cur.end());
    for (Node& cn : children)
    {
      it = cmap.find(cn);
      Assert(it != cmap.end());
      Assert(!it->second.isNull());
      childChanged = childChanged || cn != it->second;
      cn = it->second;
    }
    Node ret = cur;
    if (childChanged)
    {
      ret = rewrite(nm->mkNode(cur.getKind(), children));
    }
    cmap[cur] = ret;
  } while (!visit.empty());

  Assert(cmap.find(cur) != cmap.end());
  return cmap[cur];
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
