/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of term database class.
 */

#include "theory/quantifiers/term_database.h"

#include "expr/skolem_manager.h"
#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "options/theory_options.h"
#include "options/uf_options.h"
#include "theory/quantifiers/ematching/trigger_term_info.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/quantifiers_registry.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"
#include "theory/uf/equality_engine.h"

using namespace cvc5::kind;
using namespace cvc5::context;

namespace cvc5 {
namespace theory {
namespace quantifiers {

TermDb::TermDb(QuantifiersState& qs, QuantifiersRegistry& qr)
    : d_qstate(qs),
      d_qim(nullptr),
      d_qreg(qr),
      d_termsContext(),
      d_termsContextUse(options::termDbCd() ? qs.getSatContext()
                                            : &d_termsContext),
      d_processed(d_termsContextUse),
      d_typeMap(d_termsContextUse),
      d_ops(d_termsContextUse),
      d_opMap(d_termsContextUse),
      d_inactive_map(qs.getSatContext())
{
  d_consistent_ee = true;
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  if (!options::termDbCd())
  {
    // when not maintaining terms in a context-dependent manner, we clear during
    // each presolve, which requires maintaining a single outermost level
    d_termsContext.push();
  }
}

TermDb::~TermDb(){

}

void TermDb::finishInit(QuantifiersInferenceManager* qim) { d_qim = qim; }

void TermDb::registerQuantifier( Node q ) {
  Assert(q[0].getNumChildren() == d_qreg.getNumInstantiationConstants(q));
  for (size_t i = 0, nvars = q[0].getNumChildren(); i < nvars; i++)
  {
    Node ic = d_qreg.getInstantiationConstant(q, i);
    setTermInactive( ic );
  }
}

size_t TermDb::getNumOperators() const { return d_ops.size(); }

Node TermDb::getOperator(size_t i) const
{
  Assert(i < d_ops.size());
  return d_ops[i];
}

/** ground terms */
size_t TermDb::getNumGroundTerms(Node f) const
{
  NodeDbListMap::const_iterator it = d_opMap.find(f);
  if (it != d_opMap.end())
  {
    return it->second->d_list.size();
  }
  return 0;
}

Node TermDb::getGroundTerm(Node f, size_t i) const
{
  NodeDbListMap::const_iterator it = d_opMap.find(f);
  if (it != d_opMap.end())
  {
    Assert(i < it->second->d_list.size());
    return it->second->d_list[i];
  }
  Assert(false);
  return Node::null();
}

size_t TermDb::getNumTypeGroundTerms(TypeNode tn) const
{
  TypeNodeDbListMap::const_iterator it = d_typeMap.find(tn);
  if (it != d_typeMap.end())
  {
    return it->second->d_list.size();
  }
  return 0;
}

Node TermDb::getTypeGroundTerm(TypeNode tn, size_t i) const
{
  TypeNodeDbListMap::const_iterator it = d_typeMap.find(tn);
  if (it != d_typeMap.end())
  {
    Assert(i < it->second->d_list.size());
    return it->second->d_list[i];
  }
  Assert(false);
  return Node::null();
}

Node TermDb::getOrMakeTypeGroundTerm(TypeNode tn, bool reqVar)
{
  TypeNodeDbListMap::const_iterator it = d_typeMap.find(tn);
  if (it != d_typeMap.end())
  {
    Assert(!it->second->d_list.empty());
    if (!reqVar)
    {
      return it->second->d_list[0];
    }
    for (const Node& v : it->second->d_list)
    {
      if (v.isVar())
      {
        return v;
      }
    }
  }
  return getOrMakeTypeFreshVariable(tn);
}

Node TermDb::getOrMakeTypeFreshVariable(TypeNode tn)
{
  std::unordered_map<TypeNode, Node>::iterator it = d_type_fv.find(tn);
  if (it == d_type_fv.end())
  {
    SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
    std::stringstream ss;
    ss << language::SetLanguage(options::outputLanguage());
    ss << "e_" << tn;
    Node k = sm->mkDummySkolem(ss.str(), tn, "is a termDb fresh variable");
    Trace("mkVar") << "TermDb:: Make variable " << k << " : " << tn
                   << std::endl;
    if (options::instMaxLevel() != -1)
    {
      QuantAttributes::setInstantiationLevelAttr(k, 0);
    }
    d_type_fv[tn] = k;
    return k;
  }
  return it->second;
}

Node TermDb::getMatchOperator( Node n ) {
  Kind k = n.getKind();
  //datatype operators may be parametric, always assume they are
  if (k == SELECT || k == STORE || k == UNION || k == INTERSECTION
      || k == SUBSET || k == SETMINUS || k == MEMBER || k == SINGLETON
      || k == APPLY_SELECTOR_TOTAL || k == APPLY_SELECTOR || k == APPLY_TESTER
      || k == SEP_PTO || k == HO_APPLY || k == SEQ_NTH)
  {
    //since it is parametric, use a particular one as op
    TypeNode tn = n[0].getType();
    Node op = n.getOperator();
    std::map< Node, std::map< TypeNode, Node > >::iterator ito = d_par_op_map.find( op );
    if( ito!=d_par_op_map.end() ){
      std::map< TypeNode, Node >::iterator it = ito->second.find( tn );
      if( it!=ito->second.end() ){
        return it->second;
      }
    }
    Trace("par-op") << "Parametric operator : " << k << ", " << n.getOperator() << ", " << tn << " : " << n << std::endl;
    d_par_op_map[op][tn] = n;
    return n;
  }
  else if (inst::TriggerTermInfo::isAtomicTriggerKind(k))
  {
    return n.getOperator();
  }else{
    return Node::null();
  }
}

void TermDb::addTerm(Node n)
{
  if (d_processed.find(n) != d_processed.end())
  {
    return;
  }
  d_processed.insert(n);
  if (!TermUtil::hasInstConstAttr(n))
  {
    Trace("term-db-debug") << "register term : " << n << std::endl;
    DbList* dlt = getOrMkDbListForType(n.getType());
    dlt->d_list.push_back(n);
    // if this is an atomic trigger, consider adding it
    if (inst::TriggerTermInfo::isAtomicTrigger(n))
    {
      Trace("term-db") << "register term in db " << n << std::endl;

      Node op = getMatchOperator(n);
      Trace("term-db-debug") << "  match operator is : " << op << std::endl;
      DbList* dlo = getOrMkDbListForOp(op);
      dlo->d_list.push_back(n);
      // If we are higher-order, we may need to register more terms.
      addTermInternal(n);
    }
  }
  else
  {
    setTermInactive(n);
  }
  if (!n.isClosure())
  {
    for (const Node& nc : n)
    {
      addTerm(nc);
    }
  }
}

DbList* TermDb::getOrMkDbListForType(TypeNode tn)
{
  TypeNodeDbListMap::iterator it = d_typeMap.find(tn);
  if (it != d_typeMap.end())
  {
    return it->second.get();
  }
  std::shared_ptr<DbList> dl = std::make_shared<DbList>(d_termsContextUse);
  d_typeMap.insert(tn, dl);
  return dl.get();
}

DbList* TermDb::getOrMkDbListForOp(TNode op)
{
  NodeDbListMap::iterator it = d_opMap.find(op);
  if (it != d_opMap.end())
  {
    return it->second.get();
  }
  std::shared_ptr<DbList> dl = std::make_shared<DbList>(d_termsContextUse);
  d_opMap.insert(op, dl);
  Assert(op.getKind() != BOUND_VARIABLE);
  d_ops.push_back(op);
  return dl.get();
}

void TermDb::computeArgReps( TNode n ) {
  if (d_arg_reps.find(n) == d_arg_reps.end())
  {
    eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
    for (const TNode& nc : n)
    {
      TNode r = ee->hasTerm(nc) ? ee->getRepresentative(nc) : nc;
      d_arg_reps[n].push_back( r );
    }
  }
}

void TermDb::computeUfEqcTerms( TNode f ) {
  Assert(f == getOperatorRepresentative(f));
  if (d_func_map_eqc_trie.find(f) != d_func_map_eqc_trie.end())
  {
    return;
  }
  d_func_map_eqc_trie[f].clear();
  // get the matchable operators in the equivalence class of f
  std::vector<TNode> ops;
  getOperatorsFor(f, ops);
  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
  for (TNode ff : ops)
  {
    DbList* dbl = getOrMkDbListForOp(ff);
    for (const Node& n : dbl->d_list)
    {
      if (hasTermCurrent(n) && isTermActive(n))
      {
        computeArgReps(n);
        TNode r = ee->hasTerm(n) ? ee->getRepresentative(n) : TNode(n);
        d_func_map_eqc_trie[f].d_data[r].addTerm(n, d_arg_reps[n]);
      }
    }
  }
}

void TermDb::computeUfTerms( TNode f ) {
  if (d_op_nonred_count.find(f) != d_op_nonred_count.end())
  {
    // already computed
    return;
  }
  Assert(f == getOperatorRepresentative(f));
  d_op_nonred_count[f] = 0;
  // get the matchable operators in the equivalence class of f
  std::vector<TNode> ops;
  getOperatorsFor(f, ops);
  Trace("term-db-debug") << "computeUfTerms for " << f << std::endl;
  unsigned congruentCount = 0;
  unsigned nonCongruentCount = 0;
  unsigned alreadyCongruentCount = 0;
  unsigned relevantCount = 0;
  NodeManager* nm = NodeManager::currentNM();
  for (TNode ff : ops)
  {
    NodeDbListMap::iterator it = d_opMap.find(ff);
    if (it == d_opMap.end())
    {
      // no terms for this operator
      continue;
    }
    Trace("term-db-debug") << "Adding terms for operator " << ff << std::endl;
    for (const Node& n : it->second->d_list)
    {
      // to be added to term index, term must be relevant, and exist in EE
      if (!hasTermCurrent(n) || !d_qstate.hasTerm(n))
      {
        Trace("term-db-debug") << n << " is not relevant." << std::endl;
        continue;
      }

      relevantCount++;
      if (!isTermActive(n))
      {
        Trace("term-db-debug") << n << " is already redundant." << std::endl;
        alreadyCongruentCount++;
        continue;
      }

      computeArgReps(n);
      Trace("term-db-debug") << "Adding term " << n << " with arg reps : ";
      for (unsigned i = 0, size = d_arg_reps[n].size(); i < size; i++)
      {
        Trace("term-db-debug") << d_arg_reps[n][i] << " ";
        if (std::find(d_func_map_rel_dom[f][i].begin(),
                      d_func_map_rel_dom[f][i].end(),
                      d_arg_reps[n][i])
            == d_func_map_rel_dom[f][i].end())
        {
          d_func_map_rel_dom[f][i].push_back(d_arg_reps[n][i]);
        }
      }
      Trace("term-db-debug") << std::endl;
      Assert(d_qstate.hasTerm(n));
      Trace("term-db-debug")
          << "  and value : " << d_qstate.getRepresentative(n) << std::endl;
      Node at = d_func_map_trie[f].addOrGetTerm(n, d_arg_reps[n]);
      Assert(d_qstate.hasTerm(at));
      Trace("term-db-debug2") << "...add term returned " << at << std::endl;
      if (at != n && d_qstate.areEqual(at, n))
      {
        setTermInactive(n);
        Trace("term-db-debug") << n << " is redundant." << std::endl;
        congruentCount++;
        continue;
      }
      std::vector<Node> lits;
      if (checkCongruentDisequal(at, n, lits))
      {
        Assert(at.getNumChildren() == n.getNumChildren());
        for (size_t k = 0, size = at.getNumChildren(); k < size; k++)
        {
          if (at[k] != n[k])
          {
            lits.push_back(nm->mkNode(EQUAL, at[k], n[k]).negate());
          }
        }
        Node lem = nm->mkOr(lits);
        if (Trace.isOn("term-db-lemma"))
        {
          Trace("term-db-lemma") << "Disequal congruent terms : " << at << " "
                                 << n << "!!!!" << std::endl;
          if (!d_qstate.getValuation().needCheck())
          {
            Trace("term-db-lemma")
                << "  all theories passed with no lemmas." << std::endl;
            // we should be a full effort check, prior to theory combination
          }
          Trace("term-db-lemma") << "  add lemma : " << lem << std::endl;
        }
        d_qim->addPendingLemma(lem, InferenceId::QUANTIFIERS_TDB_DEQ_CONG);
        d_qstate.notifyInConflict();
        d_consistent_ee = false;
        return;
      }
      nonCongruentCount++;
      d_op_nonred_count[f]++;
    }
    if (Trace.isOn("tdb"))
    {
      Trace("tdb") << "Term db size [" << f << "] : " << nonCongruentCount
                   << " / ";
      Trace("tdb") << (nonCongruentCount + congruentCount) << " / "
                   << (nonCongruentCount + congruentCount
                       + alreadyCongruentCount)
                   << " / ";
      Trace("tdb") << relevantCount << " / " << it->second->d_list.size()
                   << std::endl;
    }
  }
}

Node TermDb::getOperatorRepresentative(TNode op) const { return op; }

bool TermDb::checkCongruentDisequal(TNode a, TNode b, std::vector<Node>& exp)
{
  if (d_qstate.areDisequal(a, b))
  {
    exp.push_back(a.eqNode(b));
    return true;
  }
  return false;
}

bool TermDb::inRelevantDomain( TNode f, unsigned i, TNode r ) {
  // notice if we are not higher-order, getOperatorRepresentative is a no-op
  f = getOperatorRepresentative(f);
  computeUfTerms( f );
  Assert(!d_qstate.getEqualityEngine()->hasTerm(r)
         || d_qstate.getEqualityEngine()->getRepresentative(r) == r);
  std::map< Node, std::map< unsigned, std::vector< Node > > >::iterator it = d_func_map_rel_dom.find( f );
  if( it != d_func_map_rel_dom.end() ){
    std::map< unsigned, std::vector< Node > >::iterator it2 = it->second.find( i );
    if( it2!=it->second.end() ){
      return std::find( it2->second.begin(), it2->second.end(), r )!=it2->second.end();
    }else{
      return false;
    }
  }else{
    return false;
  }
}

Node TermDb::evaluateTerm2(TNode n,
                           std::map<TNode, Node>& visited,
                           std::vector<Node>& exp,
                           bool useEntailmentTests,
                           bool computeExp,
                           bool reqHasTerm)
{
  std::map< TNode, Node >::iterator itv = visited.find( n );
  if( itv != visited.end() ){
    return itv->second;
  }
  size_t prevSize = exp.size();
  Trace("term-db-eval") << "evaluate term : " << n << std::endl;
  Node ret = n;
  if( n.getKind()==FORALL || n.getKind()==BOUND_VARIABLE ){
    //do nothing
  }
  else if (d_qstate.hasTerm(n))
  {
    Trace("term-db-eval") << "...exists in ee, return rep" << std::endl;
    ret = d_qstate.getRepresentative(n);
    if (computeExp)
    {
      if (n != ret)
      {
        exp.push_back(n.eqNode(ret));
      }
    }
    reqHasTerm = false;
  }
  else if (n.hasOperator())
  {
    std::vector<TNode> args;
    bool ret_set = false;
    Kind k = n.getKind();
    std::vector<Node> tempExp;
    for (unsigned i = 0, nchild = n.getNumChildren(); i < nchild; i++)
    {
      TNode c = evaluateTerm2(n[i],
                              visited,
                              tempExp,
                              useEntailmentTests,
                              computeExp,
                              reqHasTerm);
      if (c.isNull())
      {
        ret = Node::null();
        ret_set = true;
        break;
      }
      else if (c == d_true || c == d_false)
      {
        // short-circuiting
        if ((k == AND && c == d_false) || (k == OR && c == d_true))
        {
          ret = c;
          ret_set = true;
          reqHasTerm = false;
          break;
        }
        else if (k == ITE && i == 0)
        {
          ret = evaluateTerm2(n[c == d_true ? 1 : 2],
                              visited,
                              tempExp,
                              useEntailmentTests,
                              computeExp,
                              reqHasTerm);
          ret_set = true;
          reqHasTerm = false;
          break;
        }
      }
      if (computeExp)
      {
        exp.insert(exp.end(), tempExp.begin(), tempExp.end());
      }
      Trace("term-db-eval") << "  child " << i << " : " << c << std::endl;
      args.push_back(c);
    }
    if (ret_set)
    {
      // if we short circuited
      if (computeExp)
      {
        exp.clear();
        exp.insert(exp.end(), tempExp.begin(), tempExp.end());
      }
    }
    else
    {
      // get the (indexed) operator of n, if it exists
      TNode f = getMatchOperator(n);
      // if it is an indexed term, return the congruent term
      if (!f.isNull())
      {
        // if f is congruent to a term indexed by this class
        TNode nn = getCongruentTerm(f, args);
        Trace("term-db-eval") << "  got congruent term " << nn
                              << " from DB for " << n << std::endl;
        if (!nn.isNull())
        {
          if (computeExp)
          {
            Assert(nn.getNumChildren() == n.getNumChildren());
            for (unsigned i = 0, nchild = nn.getNumChildren(); i < nchild; i++)
            {
              if (nn[i] != n[i])
              {
                exp.push_back(nn[i].eqNode(n[i]));
              }
            }
          }
          ret = d_qstate.getRepresentative(nn);
          Trace("term-db-eval") << "return rep" << std::endl;
          ret_set = true;
          reqHasTerm = false;
          Assert(!ret.isNull());
          if (computeExp)
          {
            if (n != ret)
            {
              exp.push_back(nn.eqNode(ret));
            }
          }
        }
      }
      if( !ret_set ){
        Trace("term-db-eval") << "return rewrite" << std::endl;
        // a theory symbol or a new UF term
        if (n.getMetaKind() == metakind::PARAMETERIZED)
        {
          args.insert(args.begin(), n.getOperator());
        }
        ret = NodeManager::currentNM()->mkNode(n.getKind(), args);
        ret = Rewriter::rewrite(ret);
        if (ret.getKind() == EQUAL)
        {
          if (d_qstate.areDisequal(ret[0], ret[1]))
          {
            ret = d_false;
          }
        }
        if (useEntailmentTests)
        {
          if (ret.getKind() == EQUAL || ret.getKind() == GEQ)
          {
            Valuation& val = d_qstate.getValuation();
            for (unsigned j = 0; j < 2; j++)
            {
              std::pair<bool, Node> et = val.entailmentCheck(
                  options::TheoryOfMode::THEORY_OF_TYPE_BASED,
                  j == 0 ? ret : ret.negate());
              if (et.first)
              {
                ret = j == 0 ? d_true : d_false;
                if (computeExp)
                {
                  exp.push_back(et.second);
                }
                break;
              }
            }
          }
        }
      }
    }
  }
  // must have the term
  if (reqHasTerm && !ret.isNull())
  {
    Kind k = ret.getKind();
    if (k != OR && k != AND && k != EQUAL && k != ITE && k != NOT
        && k != FORALL)
    {
      if (!d_qstate.hasTerm(ret))
      {
        ret = Node::null();
      }
    }
  }
  Trace("term-db-eval") << "evaluated term : " << n << ", got : " << ret
                        << ", reqHasTerm = " << reqHasTerm << std::endl;
  // clear the explanation if failed
  if (computeExp && ret.isNull())
  {
    exp.resize(prevSize);
  }
  visited[n] = ret;
  return ret;
}

TNode TermDb::getEntailedTerm2(TNode n,
                               std::map<TNode, TNode>& subs,
                               bool subsRep,
                               bool hasSubs)
{
  Trace("term-db-entail") << "get entailed term : " << n << std::endl;
  if (d_qstate.hasTerm(n))
  {
    Trace("term-db-entail") << "...exists in ee, return rep " << std::endl;
    return n;
  }else if( n.getKind()==BOUND_VARIABLE ){
    if( hasSubs ){
      std::map< TNode, TNode >::iterator it = subs.find( n );
      if( it!=subs.end() ){
        Trace("term-db-entail") << "...substitution is : " << it->second << std::endl;
        if( subsRep ){
          Assert(d_qstate.hasTerm(it->second));
          Assert(d_qstate.getRepresentative(it->second) == it->second);
          return it->second;
        }
        return getEntailedTerm2(it->second, subs, subsRep, hasSubs);
      }
    }
  }else if( n.getKind()==ITE ){
    for( unsigned i=0; i<2; i++ ){
      if (isEntailed2(n[0], subs, subsRep, hasSubs, i == 0))
      {
        return getEntailedTerm2(n[i == 0 ? 1 : 2], subs, subsRep, hasSubs);
      }
    }
  }else{
    if( n.hasOperator() ){
      TNode f = getMatchOperator( n );
      if( !f.isNull() ){
        std::vector< TNode > args;
        for( unsigned i=0; i<n.getNumChildren(); i++ ){
          TNode c = getEntailedTerm2(n[i], subs, subsRep, hasSubs);
          if( c.isNull() ){
            return TNode::null();
          }
          c = d_qstate.getRepresentative(c);
          Trace("term-db-entail") << "  child " << i << " : " << c << std::endl;
          args.push_back( c );
        }
        TNode nn = getCongruentTerm(f, args);
        Trace("term-db-entail") << "  got congruent term " << nn << " for " << n << std::endl;
        return nn;
      }
    }
  }
  return TNode::null();
}

Node TermDb::evaluateTerm(TNode n,
                          bool useEntailmentTests,
                          bool reqHasTerm)
{
  std::map< TNode, Node > visited;
  std::vector<Node> exp;
  return evaluateTerm2(n, visited, exp, useEntailmentTests, false, reqHasTerm);
}

Node TermDb::evaluateTerm(TNode n,
                          std::vector<Node>& exp,
                          bool useEntailmentTests,
                          bool reqHasTerm)
{
  std::map<TNode, Node> visited;
  return evaluateTerm2(n, visited, exp, useEntailmentTests, true, reqHasTerm);
}

TNode TermDb::getEntailedTerm(TNode n,
                              std::map<TNode, TNode>& subs,
                              bool subsRep)
{
  return getEntailedTerm2(n, subs, subsRep, true);
}

TNode TermDb::getEntailedTerm(TNode n)
{
  std::map< TNode, TNode > subs;
  return getEntailedTerm2(n, subs, false, false);
}

bool TermDb::isEntailed2(
    TNode n, std::map<TNode, TNode>& subs, bool subsRep, bool hasSubs, bool pol)
{
  Trace("term-db-entail") << "Check entailed : " << n << ", pol = " << pol << std::endl;
  Assert(n.getType().isBoolean());
  if( n.getKind()==EQUAL && !n[0].getType().isBoolean() ){
    TNode n1 = getEntailedTerm2(n[0], subs, subsRep, hasSubs);
    if( !n1.isNull() ){
      TNode n2 = getEntailedTerm2(n[1], subs, subsRep, hasSubs);
      if( !n2.isNull() ){
        if( n1==n2 ){
          return pol;
        }else{
          Assert(d_qstate.hasTerm(n1));
          Assert(d_qstate.hasTerm(n2));
          if( pol ){
            return d_qstate.areEqual(n1, n2);
          }else{
            return d_qstate.areDisequal(n1, n2);
          }
        }
      }
    }
  }else if( n.getKind()==NOT ){
    return isEntailed2(n[0], subs, subsRep, hasSubs, !pol);
  }else if( n.getKind()==OR || n.getKind()==AND ){
    bool simPol = ( pol && n.getKind()==OR ) || ( !pol && n.getKind()==AND );
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if (isEntailed2(n[i], subs, subsRep, hasSubs, pol))
      {
        if( simPol ){
          return true;
        }
      }else{
        if( !simPol ){
          return false;
        }
      }
    }
    return !simPol;
  //Boolean equality here
  }else if( n.getKind()==EQUAL || n.getKind()==ITE ){
    for( unsigned i=0; i<2; i++ ){
      if (isEntailed2(n[0], subs, subsRep, hasSubs, i == 0))
      {
        unsigned ch = ( n.getKind()==EQUAL || i==0 ) ? 1 : 2;
        bool reqPol = ( n.getKind()==ITE || i==0 ) ? pol : !pol;
        return isEntailed2(n[ch], subs, subsRep, hasSubs, reqPol);
      }
    }
  }else if( n.getKind()==APPLY_UF ){
    TNode n1 = getEntailedTerm2(n, subs, subsRep, hasSubs);
    if( !n1.isNull() ){
      Assert(d_qstate.hasTerm(n1));
      if( n1==d_true ){
        return pol;
      }else if( n1==d_false ){
        return !pol;
      }else{
        return d_qstate.getRepresentative(n1) == (pol ? d_true : d_false);
      }
    }
  }else if( n.getKind()==FORALL && !pol ){
    return isEntailed2(n[1], subs, subsRep, hasSubs, pol);
  }
  return false;
}

bool TermDb::isEntailed(TNode n, bool pol)
{
  Assert(d_consistent_ee);
  std::map< TNode, TNode > subs;
  return isEntailed2(n, subs, false, false, pol);
}

bool TermDb::isEntailed(TNode n,
                        std::map<TNode, TNode>& subs,
                        bool subsRep,
                        bool pol)
{
  Assert(d_consistent_ee);
  return isEntailed2(n, subs, subsRep, true, pol);
}

bool TermDb::isTermActive( Node n ) {
  return d_inactive_map.find( n )==d_inactive_map.end(); 
  //return !n.getAttribute(NoMatchAttribute());
}

void TermDb::setTermInactive( Node n ) {
  d_inactive_map[n] = true;
  //Trace("term-db-debug2") << "set no match attribute" << std::endl;
  //NoMatchAttribute nma;
  //n.setAttribute(nma,true);
}

bool TermDb::hasTermCurrent( Node n, bool useMode ) {
  if( !useMode ){
    return d_has_map.find( n )!=d_has_map.end();
  }
  //some assertions are not sent to EE
  if (options::termDbMode() == options::TermDbMode::ALL)
  {
    return true;
  }
  else if (options::termDbMode() == options::TermDbMode::RELEVANT)
  {
    return d_has_map.find( n )!=d_has_map.end();
  }
  Assert(false) << "TermDb::hasTermCurrent: Unknown termDbMode : " << options::termDbMode();
  return false;
}

bool TermDb::isTermEligibleForInstantiation(TNode n, TNode f)
{
  if( options::instMaxLevel()!=-1 ){
    if( n.hasAttribute(InstLevelAttribute()) ){
      int64_t fml =
          f.isNull() ? -1 : d_qreg.getQuantAttributes().getQuantInstLevel(f);
      unsigned ml = fml>=0 ? fml : options::instMaxLevel();

      if( n.getAttribute(InstLevelAttribute())>ml ){
        Trace("inst-add-debug") << "Term " << n << " has instantiation level " << n.getAttribute(InstLevelAttribute());
        Trace("inst-add-debug") << ", which is more than maximum allowed level " << ml << " for this quantified formula." << std::endl;
        return false;
      }
    }else{
      if( options::instLevelInputOnly() ){
        Trace("inst-add-debug") << "Term " << n << " does not have an instantiation level." << std::endl;
        return false;
      }
    }
  }
  // it cannot have instantiation constants, which originate from
  // counterexample-guided instantiation strategies.
  return !TermUtil::hasInstConstAttr(n);
}

Node TermDb::getEligibleTermInEqc( TNode r ) {
  if( isTermEligibleForInstantiation( r, TNode::null() ) ){
    return r;
  }else{
    std::map< Node, Node >::iterator it = d_term_elig_eqc.find( r );
    if( it==d_term_elig_eqc.end() ){
      Node h;
      eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
      eq::EqClassIterator eqc_i = eq::EqClassIterator(r, ee);
      while (!eqc_i.isFinished())
      {
        TNode n = (*eqc_i);
        ++eqc_i;
        if (isTermEligibleForInstantiation(n, TNode::null()))
        {
          h = n;
          break;
        }
      }
      d_term_elig_eqc[r] = h;
      return h;
    }else{
      return it->second;
    }
  }
}

bool TermDb::resetInternal(Theory::Effort e)
{
  // do nothing
  return true;
}

bool TermDb::finishResetInternal(Theory::Effort e)
{
  // do nothing
  return true;
}

void TermDb::addTermInternal(Node n)
{
  // do nothing
}

void TermDb::getOperatorsFor(TNode f, std::vector<TNode>& ops)
{
  ops.push_back(f);
}

void TermDb::setHasTerm( Node n ) {
  Trace("term-db-debug2") << "hasTerm : " << n  << std::endl;
  if( d_has_map.find( n )==d_has_map.end() ){
    d_has_map[n] = true;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      setHasTerm( n[i] );
    }
  }
}

void TermDb::presolve() {
  if (options::incrementalSolving() && !options::termDbCd())
  {
    d_termsContext.pop();
    d_termsContext.push();
  }
}

bool TermDb::reset( Theory::Effort effort ){
  d_op_nonred_count.clear();
  d_arg_reps.clear();
  d_func_map_trie.clear();
  d_func_map_eqc_trie.clear();
  d_func_map_rel_dom.clear();
  d_consistent_ee = true;

  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();

  Assert(ee->consistent());
  // if higher-order, add equalities for the purification terms now
  if (!resetInternal(effort))
  {
    return false;
  }

  //compute has map
  if (options::termDbMode() == options::TermDbMode::RELEVANT)
  {
    d_has_map.clear();
    d_term_elig_eqc.clear();
    eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( ee );
    while( !eqcs_i.isFinished() ){
      TNode r = (*eqcs_i);
      bool addedFirst = false;
      Node first;
      //TODO: ignoring singleton eqc isn't enough, need to ensure eqc are relevant
      eq::EqClassIterator eqc_i = eq::EqClassIterator(r, ee);
      while( !eqc_i.isFinished() ){
        TNode n = (*eqc_i);
        if( first.isNull() ){
          first = n;
        }else{
          if( !addedFirst ){
            addedFirst = true;
            setHasTerm( first );
          }
          setHasTerm( n );
        }
        ++eqc_i;
      }
      ++eqcs_i;
    }
    const LogicInfo& logicInfo = d_qstate.getLogicInfo();
    for (TheoryId theoryId = THEORY_FIRST; theoryId < THEORY_LAST; ++theoryId)
    {
      if (!logicInfo.isTheoryEnabled(theoryId))
      {
        continue;
      }
      for (context::CDList<Assertion>::const_iterator
               it = d_qstate.factsBegin(theoryId),
               it_end = d_qstate.factsEnd(theoryId);
           it != it_end;
           ++it)
      {
        setHasTerm((*it).d_assertion);
      }
    }
  }
  // finish reset
  return finishResetInternal(effort);
}

TNodeTrie* TermDb::getTermArgTrie(Node f)
{
  f = getOperatorRepresentative(f);
  computeUfTerms( f );
  std::map<Node, TNodeTrie>::iterator itut = d_func_map_trie.find(f);
  if( itut!=d_func_map_trie.end() ){
    return &itut->second;
  }else{
    return NULL;
  }
}

TNodeTrie* TermDb::getTermArgTrie(Node eqc, Node f)
{
  f = getOperatorRepresentative(f);
  computeUfEqcTerms( f );
  std::map<Node, TNodeTrie>::iterator itut = d_func_map_eqc_trie.find(f);
  if( itut==d_func_map_eqc_trie.end() ){
    return NULL;
  }else{
    if( eqc.isNull() ){
      return &itut->second;
    }else{
      std::map<TNode, TNodeTrie>::iterator itute =
          itut->second.d_data.find(eqc);
      if( itute!=itut->second.d_data.end() ){
        return &itute->second;
      }else{
        return NULL;
      }
    }
  }
}

TNode TermDb::getCongruentTerm( Node f, Node n ) {
  f = getOperatorRepresentative(f);
  computeUfTerms( f );
  std::map<Node, TNodeTrie>::iterator itut = d_func_map_trie.find(f);
  if( itut!=d_func_map_trie.end() ){
    computeArgReps( n );
    return itut->second.existsTerm( d_arg_reps[n] );
  }else{
    return TNode::null();
  }
}

TNode TermDb::getCongruentTerm( Node f, std::vector< TNode >& args ) {
  f = getOperatorRepresentative(f);
  computeUfTerms( f );
  return d_func_map_trie[f].existsTerm( args );
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
