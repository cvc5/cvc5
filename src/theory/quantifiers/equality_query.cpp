/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities used for querying about equality information.
 */

#include "theory/quantifiers/equality_query.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_util.h"

using namespace std;
using namespace cvc5::internal::kind;
using namespace cvc5::context;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

EqualityQuery::EqualityQuery(Env& env, QuantifiersState& qs, FirstOrderModel* m)
    : QuantifiersUtil(env),
      d_qstate(qs),
      d_model(m),
      d_eqi_counter(context()),
      d_reset_count(0)
{
}

EqualityQuery::~EqualityQuery() {}

bool EqualityQuery::reset(Theory::Effort e)
{
  d_int_rep.clear();
  d_reset_count++;
  return true;
}

Node EqualityQuery::getInternalRepresentative(Node a, Node q, size_t index)
{
  Assert(q.isNull() || q.getKind() == FORALL);
  Node r = d_qstate.getRepresentative(a);
  if (options().quantifiers.finiteModelFind)
  {
    if( r.isConst() && quantifiers::TermUtil::containsUninterpretedConstant( r ) ){
      //map back from values assigned by model, if any
      if (d_model != nullptr)
      {
        Node tr = d_model->getRepSet()->getTermForRepresentative(r);
        if (!tr.isNull())
        {
          r = tr;
          r = d_qstate.getRepresentative(r);
        }else{
          if (r.getType().isUninterpretedSort())
          {
            Trace("internal-rep-warn") << "No representative for UF constant." << std::endl;
            //should never happen : UF constants should never escape model
            Assert(false);
          }
        }
      }
    }
  }
  TypeNode v_tn = q.isNull() ? a.getType() : q[0][index].getType();
  if (options().quantifiers.quantRepMode == options::QuantRepMode::EE)
  {
    int32_t score = getRepScore(r, q, index, v_tn);
    if (score >= 0)
    {
      return r;
    }
    // if we are not a valid representative, try to select one below
  }
  std::map<Node, Node>& v_int_rep = d_int_rep[v_tn];
  std::map<Node, Node>::const_iterator itir = v_int_rep.find(r);
  if (itir != v_int_rep.end())
  {
    return itir->second;
  }
  // find best selection for representative
  Node r_best;
  std::vector<Node> eqc;
  d_qstate.getEquivalenceClass(r, eqc);
  Trace("internal-rep-select")
      << "Choose representative for equivalence class : " << eqc
      << ", type = " << v_tn << std::endl;
  int32_t r_best_score = -1;
  for (const Node& n : eqc)
  {
    int32_t score = getRepScore(n, q, index, v_tn);
    if (score != -2)
    {
      if (r_best.isNull()
          || (score >= 0 && (r_best_score < 0 || score < r_best_score)))
      {
        r_best = n;
        r_best_score = score;
      }
    }
  }
  if (r_best.isNull())
  {
    Trace("internal-rep-warn")
        << "No valid choice for representative in eqc class " << eqc
        << std::endl;
    return Node::null();
  }
  // now, make sure that no other member of the class is an instance
  std::unordered_map<TNode, Node> cache;
  r_best = getInstance(r_best, eqc, cache);
  // store that this representative was chosen at this point
  if (d_rep_score.find(r_best) == d_rep_score.end())
  {
    d_rep_score[r_best] = d_reset_count;
  }
  Trace("internal-rep-select")
      << "...Choose " << r_best << " with score " << r_best_score
      << " and type " << r_best.getType() << std::endl;
  Assert(r_best.getType() == v_tn);
  v_int_rep[r] = r_best;
  if (TraceIsOn("internal-rep-debug"))
  {
    if (r_best != a)
    {
      Trace("internal-rep-debug")
          << "rep( " << a << " ) = " << r << ", " << std::endl;
      Trace("internal-rep-debug")
          << "int_rep( " << a << " ) = " << r_best << ", " << std::endl;
    }
  }
  return r_best;
}

//helper functions

Node EqualityQuery::getInstance(Node n,
                                const std::vector<Node>& eqc,
                                std::unordered_map<TNode, Node>& cache)
{
  if(cache.find(n) != cache.end()) {
    return cache[n];
  }
  for( size_t i=0; i<n.getNumChildren(); i++ ){
    Node nn = getInstance( n[i], eqc, cache );
    if( !nn.isNull() ){
      return cache[n] = nn;
    }
  }
  if( std::find( eqc.begin(), eqc.end(), n )!=eqc.end() ){
    return cache[n] = n;
  }else{
    return cache[n] = Node::null();
  }
}

//-2 : invalid, -1 : undesired, otherwise : smaller the score, the better
int32_t EqualityQuery::getRepScore(Node n, Node q, size_t index, TypeNode v_tn)
{
  if (quantifiers::TermUtil::hasInstConstAttr(n))
  {  // reject
    return -2;
  }
  else if (n.getType() != v_tn)
  {  // reject if incorrect type
    return -2;
  }
  else if (options().quantifiers.instMaxLevel != -1)
  {
    //score prefer lowest instantiation level
    if( n.hasAttribute(InstLevelAttribute()) ){
      return n.getAttribute(InstLevelAttribute());
    }
    return -1;
  }
  else if (options().quantifiers.quantRepMode == options::QuantRepMode::FIRST)
  {
    // score prefers earliest use of this term as a representative
    return d_rep_score.find(n) == d_rep_score.end() ? -1 : d_rep_score[n];
  }
  else if (options().quantifiers.quantRepMode == options::QuantRepMode::DEPTH)
  {
    return quantifiers::TermUtil::getTermDepth(n);
  }
  // no preference
  return 0;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
