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

#include "expr/subs.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/skolemize.h"
#include "expr/skolem_manager.h"
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
}

void InstStrategyMbqi::reset_round(Theory::Effort e)
{
  d_freshVarType.clear();
  d_quantChecked.clear();
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
  Skolemize* skm = d_qim.getSkolemize();
  std::vector<TNode> visit;
  for (size_t i = 0, nquant = fm->getNumAssertedQuantifiers(); i < nquant; i++)
  {
    Node q = fm->getAssertedQuantifier(i);
    Trace("mb-oracle-assert") << "  * " << q << std::endl;
    Node skb = skm->getSkolemizedBody(q);
    // cannot contain (nested) quantifiers
    /*
    if( QuantifiersRewriter::containsQuantifiers( skb ) )
    {
      Trace("mb-oracle") << "...fail due to nested quantification in " << q <<
    std::endl; return;
    }
    */
    // will collect free variables for q
    visit.push_back(q[1]);
    disj.push_back(skb.negate());
  }

  if (disj.empty())
  {
    // trivially succeeds
    Trace("mb-oracle") << "...no asserted quantified formulas." << std::endl;
    return;
  }

  NodeManager* nm = NodeManager::currentNM();
  Node query = nm->mkOr(disj);

  // now collect free variables and substitute the model
  std::vector<Node> new_asserts;
  Trace("mb-oracle") << "  construct the model substitution...\n";
  Subs subs;
  std::unordered_set<TNode> visited;
  std::unordered_map<TNode, Node> mval_visited;
  TNode cur;
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      Kind ck = cur.getKind();
      TNode var;
      if (cur.isVar() && ck != BOUND_VARIABLE)
      {
        var = cur;
      }
      if (!var.isNull())
      {
        Node mvar = fm->getValue(var);
        Trace("mb-oracle-model") << "  M[" << var << "] = " << mvar << "\n";
        // must remove unhandled terms from model value
        // this includes uninterpreted constants and array constants
        Node cleanMVar = cleanModelValue(mvar, mval_visited);
        if (cleanMVar.isNull())
        {
          Trace("mb-oracle")
              << "...unhandled model value " << mvar << std::endl;
          return;
        }
        subs.add(var, cleanMVar);
      }
      if (cur.getKind()==APPLY_UF)
      {
        visit.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
        visit.push_back(cn);
      }
    }
  } while (!visit.empty());

  if (!subs.empty())
  {
    query = subs.apply(query);
  }
  query = rewrite(query);
  if (query.isConst())
  {
    Trace("mb-oracle") << "  ...query simplifies to constant " << query
                       << std::endl;
    return;
  }
  // also include distinctness of variables introduced as constants
  for (const std::pair<const TypeNode, std::unordered_set<Node> >& fv :
       d_freshVarType)
  {
    Assert(!fv.second.empty());
    if (fv.second.size() > 1)
    {
      std::vector<Node> vars(fv.second.begin(), fv.second.end());
      new_asserts.push_back(nm->mkNode(DISTINCT, vars));
    }
  }

  // finalize the query with the new assertions
  if (!new_asserts.empty())
  {
    new_asserts.push_back(query);
    query = nm->mkNode(AND, new_asserts);
  }

  // make a separate smt call
  Trace("mb-oracle") << "  make the satisfiability call...\n";
  Trace("mb-oracle-debug") << "  ...query is : " << query << std::endl;
  std::unique_ptr<SolverEngine> mbqiChecker;
  initializeSubsolver(mbqiChecker, d_env);
  mbqiChecker->assertFormula(query);
  Trace("mb-oracle") << "*** Check sat..." << std::endl;
  Result r = mbqiChecker->checkSat();
  Trace("mb-oracle") << "  ...got : " << r << std::endl;
  if (r.getStatus() != Result::UNSAT)
  {
    return;
  }
}

bool InstStrategyMbqi::checkCompleteFor(Node q) { return d_quantChecked.find(q)!=d_quantChecked.end(); }

Node InstStrategyMbqi::cleanModelValue(Node n,
                                       std::unordered_map<TNode, Node> visited)
{
  std::unordered_map<TNode, Node>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      Kind ck = cur.getKind();
      if (ck == UNINTERPRETED_SORT_VALUE)
      {
        Assert(cur.getType().isUninterpretedSort());
        // return the fresh variable for this term
        visited[cur] = getOrMkFreshVariableFor(cur);
      }
      else if (ck == CODATATYPE_BOUND_VARIABLE || ck == STORE_ALL)
      {
        // do not support array or recursive codatatype constants
        return Node::null();
      }
      else
      {
        visited[cur] = Node::null();
        visit.push_back(cur);
        for (const Node& cn : cur)
        {
          visit.push_back(cn);
        }
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        ret = NodeManager::currentNM()->mkNode(cur.getKind(), children);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

Node InstStrategyMbqi::getOrMkFreshVariableFor(Node n)
{
  NodeManager * nm = NodeManager::currentNM();
  SkolemManager * sm = nm->getSkolemManager();
  TypeNode tn = n.getType();
  Assert (tn.isUninterpretedSort());
  Node k = sm->mkPurifySkolem(n, "mbk");
  d_freshVarType[tn].insert(k);
  return k;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
