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
                   TermRegistry& tr) : QuantifiersModule(env, qs, qim, qr, tr), d_check_success(false)
{

}

void InstStrategyMbqi::reset_round( Theory::Effort e )
{
  d_check_success = false;
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
  if( e!=Theory::EFFORT_LAST_CALL || quant_e != QEFFORT_MODEL )
  {
    return;
  }
  Trace("mb-oracle") << "Run model-based oracle..." << std::endl;
  
  Trace("mb-oracle") << "  get the asserted quantified formulas...\n";
  // see if the negation of each quantified formula is satisfiable in the model
  std::vector< Node > disj;
  FirstOrderModel * fm = d_treg.getModel();
  Skolemize * skm = d_qim.getSkolemize();
  std::vector<TNode> visit;
  for( size_t i=0, nquant = fm->getNumAssertedQuantifiers(); i<nquant; i++ )
  {
    Node q = fm->getAssertedQuantifier( i );
    Trace("mb-oracle-assert") << "  * " << q << std::endl;
    Node skb = skm->getSkolemizedBody(q);
    // cannot contain (nested) quantifiers
    /*
    if( QuantifiersRewriter::containsQuantifiers( skb ) )
    {
      Trace("mb-oracle") << "...fail due to nested quantification in " << q << std::endl;
      return;
    }
    */
    // will collect free variables for q
    visit.push_back(q[1]);
    disj.push_back(skb.negate());
  }
  
  if( disj.empty() )
  {
    // trivially succeeds
    Trace("mb-oracle") << "...no asserted quantified formulas." << std::endl;
    return;
  }
  
  NodeManager * nm = NodeManager::currentNM();
  Node query = nm->mkOr(disj);
  
  // now collect free variables and substitute the model
  std::vector< Node > new_asserts;
  Trace("mb-oracle") << "  construct the model substitution...\n";
  std::unordered_set< TNode > op_proc;
  std::vector< Node > vars;
  std::vector< Node > subs;
  std::unordered_set<TNode> visited;
  std::unordered_map<TNode, Node> mval_visited;
  TNode cur;
  do {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end()) {
      visited.insert(cur);
      Kind ck = cur.getKind();
      TNode var;
      if( cur.isVar() && ck!=BOUND_VARIABLE )
      {
        var = cur;
      }
      else if( ck==APPLY_UF )
      {
        TNode op = cur.getOperator();
        if( op_proc.find(op)==op_proc.end() )
        {
          op_proc.insert(op);
          var = op;
        }
      }
      if( !var.isNull() )
      {
        vars.push_back(var);
        Node mvar = fm->getValue(var);
        Trace("mb-oracle-model") << "  M[" << var << "] = " << mvar << "\n";
        // must remove unhandled terms from model value
        // this includes uninterpreted constants and array constants
        Node cleanMVar = cleanModelValue(mvar,mval_visited);
        if( cleanMVar.isNull() )
        {
          Trace("mb-oracle") << "...unhandled model value " << mvar << std::endl;
          return;
        }
        subs.push_back(cleanMVar);
      }
      for (const Node& cn : cur ){
        visit.push_back(cn);
      }
    }
  } while (!visit.empty());
  
  if( !vars.empty() )
  {
    query = query.substitute(vars.begin(),vars.end(),subs.begin(),subs.end());
  }
  query = rewrite( query );
  if( query.isConst() )
  {
    Trace("mb-oracle") << "  ...query simplifies to constant " << query << std::endl;
    d_check_success = !query.getConst<bool>();
    return;
  }
  // also include distinctness of variables introduced as constants
  for( const std::pair< const TypeNode, std::vector< Node > >& fv : d_fresh_var_type )
  {
    Assert( !fv.second.empty() );
    if( fv.second.size()>1 )
    {
      new_asserts.push_back( nm->mkNode( DISTINCT, fv.second ) );
    }
  }
  
  // finalize the query with the new assertions
  if( !new_asserts.empty() )
  {
    new_asserts.push_back(query);
    query = nm->mkNode(AND,new_asserts);
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
  // the model satisfies all asserted quantified formulas
  d_check_success = true;
}

bool InstStrategyMbqi::checkCompleteFor( Node q )
{
  return d_check_success;
}

Node InstStrategyMbqi::cleanModelValue( Node n, std::unordered_map<TNode, Node> visited)
{
  std::unordered_map<TNode, Node>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end()) {
      Kind ck = cur.getKind();
      if( ck==UNINTERPRETED_SORT_VALUE )
      {
        TypeNode ctn = cur.getType();
        if( !ctn.isUninterpretedSort() )
        {
          return Node::null();
        }
        // return the fresh variable for this term
        visited[cur] = getOrMkFreshVariableFor(cur);
      }
      else if (ck==CODATATYPE_BOUND_VARIABLE || ck==STORE_ALL )
      {
        // do not support array or recursive codatatype constants
        return Node::null();
      }
      else
      {
        visited[cur] = Node::null();
        visit.push_back(cur);
        for (const Node& cn : cur) {
          visit.push_back(cn);
        }
      }
    } else if (it->second.isNull()) {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED) {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur) {
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
  std::unordered_map< Node, Node >::iterator it = d_fresh_var.find(n);
  if( it != d_fresh_var.end() )
  {
    return it->second;
  }
  TypeNode tn = n.getType();
  // FIXME
  Node k;// = NodeManager::currentNM()->mkSkolem("mbk",tn);
  d_fresh_var_type[tn].push_back(k);
  d_fresh_var[n] = k;
  return k;
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
