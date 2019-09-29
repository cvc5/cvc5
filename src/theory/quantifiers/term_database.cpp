/*********************                                                        */
/*! \file term_database.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of term databse class
 **/

#include "theory/quantifiers/term_database.h"

#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "options/uf_options.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers/ematching/trigger.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory::inst;

namespace CVC4 {
namespace theory {
namespace quantifiers {

TermDb::TermDb(context::Context* c, context::UserContext* u,
               QuantifiersEngine* qe)
    : d_quantEngine(qe),
      d_inactive_map(c) {
  d_consistent_ee = true;
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

TermDb::~TermDb(){

}

void TermDb::registerQuantifier( Node q ) {
  Assert( q[0].getNumChildren()==d_quantEngine->getTermUtil()->getNumInstantiationConstants( q ) );
  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
    Node ic = d_quantEngine->getTermUtil()->getInstantiationConstant( q, i );
    setTermInactive( ic );
  }
}

unsigned TermDb::getNumOperators() { return d_ops.size(); }
Node TermDb::getOperator(unsigned i)
{
  Assert(i < d_ops.size());
  return d_ops[i];
}

/** ground terms */
unsigned TermDb::getNumGroundTerms(Node f) const
{
  std::map<Node, std::vector<Node> >::const_iterator it = d_op_map.find(f);
  if( it!=d_op_map.end() ){
    return it->second.size();
  }else{
    return 0;
  }
}

Node TermDb::getGroundTerm(Node f, unsigned i) const
{
  std::map<Node, std::vector<Node> >::const_iterator it = d_op_map.find(f);
  if (it != d_op_map.end())
  {
    Assert(i < it->second.size());
    return it->second[i];
  }
  else
  {
    Assert(false);
    return Node::null();
  }
}

unsigned TermDb::getNumTypeGroundTerms(TypeNode tn) const
{
  std::map<TypeNode, std::vector<Node> >::const_iterator it =
      d_type_map.find(tn);
  if( it!=d_type_map.end() ){
    return it->second.size();
  }else{
    return 0;
  }
}

Node TermDb::getTypeGroundTerm(TypeNode tn, unsigned i) const
{
  std::map<TypeNode, std::vector<Node> >::const_iterator it =
      d_type_map.find(tn);
  if (it != d_type_map.end())
  {
    Assert(i < it->second.size());
    return it->second[i];
  }
  else
  {
    Assert(false);
    return Node::null();
  }
}

Node TermDb::getOrMakeTypeGroundTerm(TypeNode tn, bool reqVar)
{
  std::map<TypeNode, std::vector<Node> >::const_iterator it =
      d_type_map.find(tn);
  if (it != d_type_map.end())
  {
    Assert(!it->second.empty());
    if (!reqVar)
    {
      return it->second[0];
    }
    for (const Node& v : it->second)
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
  std::unordered_map<TypeNode, Node, TypeNodeHashFunction>::iterator it =
      d_type_fv.find(tn);
  if (it == d_type_fv.end())
  {
    std::stringstream ss;
    ss << language::SetLanguage(options::outputLanguage());
    ss << "e_" << tn;
    Node k = NodeManager::currentNM()->mkSkolem(
        ss.str(), tn, "is a termDb fresh variable");
    Trace("mkVar") << "TermDb:: Make variable " << k << " : " << tn
                   << std::endl;
    if (options::instMaxLevel() != -1)
    {
      QuantAttributes::setInstantiationLevelAttr(k, 0);
    }
    d_type_fv[tn] = k;
    return k;
  }
  else
  {
    return it->second;
  }
}

Node TermDb::getMatchOperator( Node n ) {
  Kind k = n.getKind();
  //datatype operators may be parametric, always assume they are
  if( k==SELECT || k==STORE || k==UNION || k==INTERSECTION || k==SUBSET || k==SETMINUS || k==MEMBER || k==SINGLETON || 
      k==APPLY_SELECTOR_TOTAL || k==APPLY_TESTER || k==SEP_PTO || k==HO_APPLY ){
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
  }else if( inst::Trigger::isAtomicTriggerKind( k ) ){
    return n.getOperator();
  }else{
    return Node::null();
  }
}

void TermDb::addTerm(Node n,
                     std::set<Node>& added,
                     bool withinQuant,
                     bool withinInstClosure)
{
  //don't add terms in quantifier bodies
  if( withinQuant && !options::registerQuantBodyTerms() ){
    return;
  }
  bool rec = false;
  if (d_processed.find(n) == d_processed.end())
  {
    d_processed.insert(n);
    if (!TermUtil::hasInstConstAttr(n))
    {
      Trace("term-db-debug") << "register term : " << n << std::endl;
      d_type_map[n.getType()].push_back(n);
      // if this is an atomic trigger, consider adding it
      if (inst::Trigger::isAtomicTrigger(n))
      {
        Trace("term-db") << "register term in db " << n << std::endl;

        Node op = getMatchOperator(n);
        Trace("term-db-debug") << "  match operator is : " << op << std::endl;
        if (d_op_map.find(op) == d_op_map.end())
        {
          d_ops.push_back(op);
        }
        d_op_map[op].push_back(n);
        added.insert(n);
        // If we are higher-order, we may need to register more terms.
        if (options::ufHo())
        {
          addTermHo(n, added, withinQuant, withinInstClosure);
        }
      }
    }
    else
    {
      setTermInactive(n);
    }
    rec = true;
  }
  if (withinInstClosure
      && d_iclosure_processed.find(n) == d_iclosure_processed.end())
  {
    d_iclosure_processed.insert(n);
    rec = true;
  }
  if (rec && !n.isClosure())
  {
    for (const Node& nc : n)
    {
      addTerm(nc, added, withinQuant, withinInstClosure);
    }
  }
}

void TermDb::computeArgReps( TNode n ) {
  if (d_arg_reps.find(n) == d_arg_reps.end())
  {
    eq::EqualityEngine * ee = d_quantEngine->getActiveEqualityEngine();
    for (const TNode& nc : n)
    {
      TNode r = ee->hasTerm(nc) ? ee->getRepresentative(nc) : nc;
      d_arg_reps[n].push_back( r );
    }
  }
}

void TermDb::computeUfEqcTerms( TNode f ) {
  Assert( f==getOperatorRepresentative( f ) );
  if (d_func_map_eqc_trie.find(f) != d_func_map_eqc_trie.end())
  {
    return;
  }
  d_func_map_eqc_trie[f].clear();
  // get the matchable operators in the equivalence class of f
  std::vector<TNode> ops;
  ops.push_back(f);
  if (options::ufHo())
  {
    ops.insert(ops.end(), d_ho_op_slaves[f].begin(), d_ho_op_slaves[f].end());
  }
  eq::EqualityEngine* ee = d_quantEngine->getActiveEqualityEngine();
  for (const Node& ff : ops)
  {
    for (const TNode& n : d_op_map[ff])
    {
      if (hasTermCurrent(n) && isTermActive(n))
      {
        computeArgReps(n);
        TNode r = ee->hasTerm(n) ? ee->getRepresentative(n) : n;
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
  Assert( f==getOperatorRepresentative( f ) );
  d_op_nonred_count[f] = 0;
  // get the matchable operators in the equivalence class of f
  std::vector<TNode> ops;
  ops.push_back(f);
  if (options::ufHo())
  {
    ops.insert(ops.end(), d_ho_op_slaves[f].begin(), d_ho_op_slaves[f].end());
  }
  Trace("term-db-debug") << "computeUfTerms for " << f << std::endl;
  unsigned congruentCount = 0;
  unsigned nonCongruentCount = 0;
  unsigned alreadyCongruentCount = 0;
  unsigned relevantCount = 0;
  eq::EqualityEngine* ee = d_quantEngine->getActiveEqualityEngine();
  NodeManager* nm = NodeManager::currentNM();
  for (const Node& ff : ops)
  {
    std::map<Node, std::vector<Node> >::iterator it = d_op_map.find(ff);
    if (it == d_op_map.end())
    {
      // no terms for this operator
      continue;
    }
    Trace("term-db-debug") << "Adding terms for operator " << ff << std::endl;
    for (const Node& n : it->second)
    {
      // to be added to term index, term must be relevant, and exist in EE
      if (!hasTermCurrent(n) || !ee->hasTerm(n))
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
      Assert(ee->hasTerm(n));
      Trace("term-db-debug") << "  and value : " << ee->getRepresentative(n)
                             << std::endl;
      Node at = d_func_map_trie[f].addOrGetTerm(n, d_arg_reps[n]);
      Assert(ee->hasTerm(at));
      Trace("term-db-debug2") << "...add term returned " << at << std::endl;
      if (at != n && ee->areEqual(at, n))
      {
        setTermInactive(n);
        Trace("term-db-debug") << n << " is redundant." << std::endl;
        congruentCount++;
        continue;
      }
      if (ee->areDisequal(at, n, false))
      {
        std::vector<Node> lits;
        lits.push_back(nm->mkNode(EQUAL, at, n));
        bool success = true;
        if (options::ufHo())
        {
          // operators might be disequal
          if (ops.size() > 1)
          {
            Node atf = getMatchOperator(at);
            Node nf = getMatchOperator(n);
            if (atf != nf)
            {
              if (at.getKind() == APPLY_UF && n.getKind() == APPLY_UF)
              {
                lits.push_back(atf.eqNode(nf).negate());
              }
              else
              {
                success = false;
                Assert(false);
              }
            }
          }
        }
        if (success)
        {
          Assert(at.getNumChildren() == n.getNumChildren());
          for (unsigned k = 0, size = at.getNumChildren(); k < size; k++)
          {
            if (at[k] != n[k])
            {
              lits.push_back(nm->mkNode(EQUAL, at[k], n[k]).negate());
            }
          }
          Node lem = lits.size() == 1 ? lits[0] : nm->mkNode(OR, lits);
          if (Trace.isOn("term-db-lemma"))
          {
            Trace("term-db-lemma") << "Disequal congruent terms : " << at << " "
                                   << n << "!!!!" << std::endl;
            if (!d_quantEngine->getTheoryEngine()->needCheck())
            {
              Trace("term-db-lemma") << "  all theories passed with no lemmas."
                                     << std::endl;
              // we should be a full effort check, prior to theory combination
            }
            Trace("term-db-lemma") << "  add lemma : " << lem << std::endl;
          }
          d_quantEngine->addLemma(lem);
          d_quantEngine->setConflict();
          d_consistent_ee = false;
          return;
        }
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
      Trace("tdb") << relevantCount << " / " << it->second.size() << std::endl;
    }
  }
}

void TermDb::addTermHo(Node n,
                       std::set<Node>& added,
                       bool withinQuant,
                       bool withinInstClosure)
{
  Assert(options::ufHo());
  if (n.getType().isFunction())
  {
    // nothing special to do with functions
    return;
  }
  NodeManager* nm = NodeManager::currentNM();
  Node curr = n;
  std::vector<Node> args;
  while (curr.getKind() == HO_APPLY)
  {
    args.insert(args.begin(), curr[1]);
    curr = curr[0];
    if (!curr.isVar())
    {
      // purify the term
      std::map<Node, Node>::iterator itp = d_ho_fun_op_purify.find(curr);
      Node psk;
      if (itp == d_ho_fun_op_purify.end())
      {
        psk = nm->mkSkolem("pfun",
                           curr.getType(),
                           "purify for function operator term indexing");
        d_ho_fun_op_purify[curr] = psk;
        // we do not add it to d_ops since it is an internal operator
      }
      else
      {
        psk = itp->second;
      }
      std::vector<Node> children;
      children.push_back(psk);
      children.insert(children.end(), args.begin(), args.end());
      Node p_n = nm->mkNode(APPLY_UF, children);
      Trace("term-db") << "register term in db (via purify) " << p_n
                       << std::endl;
      // also add this one internally
      d_op_map[psk].push_back(p_n);
      // maintain backwards mapping
      d_ho_purify_to_term[p_n] = n;
    }
  }
  if (!args.empty() && curr.isVar())
  {
    // also add standard application version
    args.insert(args.begin(), curr);
    Node uf_n = nm->mkNode(APPLY_UF, args);
    addTerm(uf_n, added, withinQuant, withinInstClosure);
  }
}

Node TermDb::getOperatorRepresentative( TNode op ) const {
  std::map< TNode, TNode >::const_iterator it = d_ho_op_rep.find( op );
  if( it!=d_ho_op_rep.end() ){
    return it->second;
  }else{
    return op;
  }
}

bool TermDb::inRelevantDomain( TNode f, unsigned i, TNode r ) {
  if( options::ufHo() ){
    f = getOperatorRepresentative( f );
  }
  computeUfTerms( f );
  Assert( !d_quantEngine->getActiveEqualityEngine()->hasTerm( r ) || 
          d_quantEngine->getActiveEqualityEngine()->getRepresentative( r )==r );
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
                           EqualityQuery* qy,
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
  else if (qy->hasTerm(n))
  {
    Trace("term-db-eval") << "...exists in ee, return rep" << std::endl;
    ret = qy->getRepresentative(n);
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
                              qy,
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
                              qy,
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
        TNode nn = qy->getCongruentTerm(f, args);
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
          ret = qy->getRepresentative(nn);
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
          if (qy->areDisequal(ret[0], ret[1]))
          {
            ret = d_false;
          }
        }
        if (useEntailmentTests)
        {
          if (ret.getKind() == EQUAL || ret.getKind() == GEQ)
          {
            TheoryEngine* te = d_quantEngine->getTheoryEngine();
            for (unsigned j = 0; j < 2; j++)
            {
              std::pair<bool, Node> et = te->entailmentCheck(
                  THEORY_OF_TYPE_BASED, j == 0 ? ret : ret.negate());
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
      if (!qy->hasTerm(ret))
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


TNode TermDb::getEntailedTerm2( TNode n, std::map< TNode, TNode >& subs, bool subsRep, bool hasSubs, EqualityQuery * qy ) {
  Assert( !qy->extendsEngine() );
  Trace("term-db-entail") << "get entailed term : " << n << std::endl;
  if( qy->getEngine()->hasTerm( n ) ){
    Trace("term-db-entail") << "...exists in ee, return rep " << std::endl;
    return n;
  }else if( n.getKind()==BOUND_VARIABLE ){
    if( hasSubs ){
      std::map< TNode, TNode >::iterator it = subs.find( n );
      if( it!=subs.end() ){
        Trace("term-db-entail") << "...substitution is : " << it->second << std::endl;
        if( subsRep ){
          Assert( qy->getEngine()->hasTerm( it->second ) );
          Assert( qy->getEngine()->getRepresentative( it->second )==it->second );
          return it->second;
        }else{
          return getEntailedTerm2( it->second, subs, subsRep, hasSubs, qy );
        }
      }
    }
  }else if( n.getKind()==ITE ){
    for( unsigned i=0; i<2; i++ ){
      if( isEntailed2( n[0], subs, subsRep, hasSubs, i==0, qy ) ){
        return getEntailedTerm2( n[ i==0 ? 1 : 2 ], subs, subsRep, hasSubs, qy );
      }
    }
  }else{
    if( n.hasOperator() ){
      TNode f = getMatchOperator( n );
      if( !f.isNull() ){
        std::vector< TNode > args;
        for( unsigned i=0; i<n.getNumChildren(); i++ ){
          TNode c = getEntailedTerm2( n[i], subs, subsRep, hasSubs, qy );
          if( c.isNull() ){
            return TNode::null();
          }
          c = qy->getEngine()->getRepresentative( c );
          Trace("term-db-entail") << "  child " << i << " : " << c << std::endl;
          args.push_back( c );
        }
        TNode nn = qy->getCongruentTerm( f, args );
        Trace("term-db-entail") << "  got congruent term " << nn << " for " << n << std::endl;
        return nn;
      }
    }
  }
  return TNode::null();
}

Node TermDb::evaluateTerm(TNode n,
                          EqualityQuery* qy,
                          bool useEntailmentTests,
                          bool reqHasTerm)
{
  if( qy==NULL ){
    qy = d_quantEngine->getEqualityQuery();
  }
  std::map< TNode, Node > visited;
  std::vector<Node> exp;
  return evaluateTerm2(
      n, visited, exp, qy, useEntailmentTests, false, reqHasTerm);
}

Node TermDb::evaluateTerm(TNode n,
                          std::vector<Node>& exp,
                          EqualityQuery* qy,
                          bool useEntailmentTests,
                          bool reqHasTerm)
{
  if (qy == NULL)
  {
    qy = d_quantEngine->getEqualityQuery();
  }
  std::map<TNode, Node> visited;
  return evaluateTerm2(
      n, visited, exp, qy, useEntailmentTests, true, reqHasTerm);
}

TNode TermDb::getEntailedTerm( TNode n, std::map< TNode, TNode >& subs, bool subsRep, EqualityQuery * qy ) {
  if( qy==NULL ){
    qy = d_quantEngine->getEqualityQuery();
  }
  return getEntailedTerm2( n, subs, subsRep, true, qy );
}

TNode TermDb::getEntailedTerm( TNode n, EqualityQuery * qy ) {
  if( qy==NULL ){
    qy = d_quantEngine->getEqualityQuery();
  }
  std::map< TNode, TNode > subs;
  return getEntailedTerm2( n, subs, false, false, qy );
}

bool TermDb::isEntailed2( TNode n, std::map< TNode, TNode >& subs, bool subsRep, bool hasSubs, bool pol, EqualityQuery * qy ) {
  Assert( !qy->extendsEngine() );
  Trace("term-db-entail") << "Check entailed : " << n << ", pol = " << pol << std::endl;
  Assert( n.getType().isBoolean() );
  if( n.getKind()==EQUAL && !n[0].getType().isBoolean() ){
    TNode n1 = getEntailedTerm2( n[0], subs, subsRep, hasSubs, qy );
    if( !n1.isNull() ){
      TNode n2 = getEntailedTerm2( n[1], subs, subsRep, hasSubs, qy );
      if( !n2.isNull() ){
        if( n1==n2 ){
          return pol;
        }else{
          Assert( qy->getEngine()->hasTerm( n1 ) );
          Assert( qy->getEngine()->hasTerm( n2 ) );
          if( pol ){
            return qy->getEngine()->areEqual( n1, n2 );
          }else{
            return qy->getEngine()->areDisequal( n1, n2, false );
          }
        }
      }
    }
  }else if( n.getKind()==NOT ){
    return isEntailed2( n[0], subs, subsRep, hasSubs, !pol, qy );
  }else if( n.getKind()==OR || n.getKind()==AND ){
    bool simPol = ( pol && n.getKind()==OR ) || ( !pol && n.getKind()==AND );
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( isEntailed2( n[i], subs, subsRep, hasSubs, pol, qy ) ){
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
      if( isEntailed2( n[0], subs, subsRep, hasSubs, i==0, qy ) ){
        unsigned ch = ( n.getKind()==EQUAL || i==0 ) ? 1 : 2;
        bool reqPol = ( n.getKind()==ITE || i==0 ) ? pol : !pol;
        return isEntailed2( n[ch], subs, subsRep, hasSubs, reqPol, qy );
      }
    }
  }else if( n.getKind()==APPLY_UF ){
    TNode n1 = getEntailedTerm2( n, subs, subsRep, hasSubs, qy );
    if( !n1.isNull() ){
      Assert( qy->hasTerm( n1 ) );
      if( n1==d_true ){
        return pol;
      }else if( n1==d_false ){
        return !pol;
      }else{
        return qy->getEngine()->getRepresentative( n1 ) == ( pol ? d_true : d_false );
      }
    }
  }else if( n.getKind()==FORALL && !pol ){
    return isEntailed2( n[1], subs, subsRep, hasSubs, pol, qy );
  }
  return false;
}

bool TermDb::isEntailed( TNode n, bool pol, EqualityQuery * qy ) {
  if( qy==NULL ){
    Assert( d_consistent_ee );
    qy = d_quantEngine->getEqualityQuery();
  }
  std::map< TNode, TNode > subs;
  return isEntailed2( n, subs, false, false, pol, qy );
}

bool TermDb::isEntailed( TNode n, std::map< TNode, TNode >& subs, bool subsRep, bool pol, EqualityQuery * qy ) {
  if( qy==NULL ){
    Assert( d_consistent_ee );
    qy = d_quantEngine->getEqualityQuery();
  }
  return isEntailed2( n, subs, subsRep, true, pol, qy );
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
  }else{
    //return d_quantEngine->getActiveEqualityEngine()->hasTerm( n ); //some assertions are not sent to EE
    if( options::termDbMode()==TERM_DB_ALL ){
      return true;
    }else if( options::termDbMode()==TERM_DB_RELEVANT ){
      return d_has_map.find( n )!=d_has_map.end();
    }else{
      Assert( false );
      return false;
    }
  }
}

bool TermDb::isTermEligibleForInstantiation(TNode n, TNode f)
{
  if( options::lteRestrictInstClosure() ){
    //has to be both in inst closure and in ground assertions
    if( !isInstClosure( n ) ){
      Trace("inst-add-debug") << "Term " << n << " is not an inst-closure term." << std::endl;
      return false;
    }
    // hack : since theories preregister terms not in assertions, we are using hasTermCurrent to approximate this
    if( !hasTermCurrent( n, false ) ){
      Trace("inst-add-debug") << "Term " << n << " is not in a ground assertion." << std::endl;
      return false;
    }
  }
  if( options::instMaxLevel()!=-1 ){
    if( n.hasAttribute(InstLevelAttribute()) ){
      int fml = f.isNull() ? -1 : d_quantEngine->getQuantAttributes()->getQuantInstLevel( f );
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
      eq::EqualityEngine* ee = d_quantEngine->getActiveEqualityEngine();
      eq::EqClassIterator eqc_i = eq::EqClassIterator( r, ee );
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

bool TermDb::isInstClosure( Node r ) {
  return d_iclosure_processed.find( r )!=d_iclosure_processed.end();
}

void TermDb::setHasTerm( Node n ) {
  Trace("term-db-debug2") << "hasTerm : " << n  << std::endl;
  //if( inst::Trigger::isAtomicTrigger( n ) ){
  if( d_has_map.find( n )==d_has_map.end() ){
    d_has_map[n] = true;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      setHasTerm( n[i] );
    }
  }
}

void TermDb::presolve() {
  if( options::incrementalSolving() ){
    // reset the caches that are SAT context-independent but user
    // context-dependent
    d_ops.clear();
    d_op_map.clear();
    d_type_map.clear();
    d_processed.clear();
    d_iclosure_processed.clear();
  }
}

bool TermDb::reset( Theory::Effort effort ){
  d_op_nonred_count.clear();
  d_arg_reps.clear();
  d_func_map_trie.clear();
  d_func_map_eqc_trie.clear();
  d_func_map_rel_dom.clear();
  d_consistent_ee = true;

  eq::EqualityEngine* ee = d_quantEngine->getActiveEqualityEngine();

  Assert(ee->consistent());
  // if higher-order, add equalities for the purification terms now
  if (options::ufHo())
  {
    Trace("quant-ho")
        << "TermDb::reset : assert higher-order purify equalities..."
        << std::endl;
    for (std::pair<const Node, Node>& pp : d_ho_purify_to_term)
    {
      if (ee->hasTerm(pp.second)
          && (!ee->hasTerm(pp.first) || !ee->areEqual(pp.second, pp.first)))
      {
        Node eq;
        std::map<Node, Node>::iterator itpe = d_ho_purify_to_eq.find(pp.first);
        if (itpe == d_ho_purify_to_eq.end())
        {
          eq = Rewriter::rewrite(pp.first.eqNode(pp.second));
          d_ho_purify_to_eq[pp.first] = eq;
        }
        else
        {
          eq = itpe->second;
        }
        Trace("quant-ho") << "- assert purify equality : " << eq << std::endl;
        ee->assertEquality(eq, true, eq);
        if (!ee->consistent())
        {
          // In some rare cases, purification functions (in the domain of
          // d_ho_purify_to_term) may escape the term database. For example,
          // matching algorithms may construct instantiations involving these
          // functions. As a result, asserting these equalities internally may
          // cause a conflict. In this case, we insist that the purification
          // equality is sent out as a lemma here.
          Trace("term-db-lemma")
              << "Purify equality lemma: " << eq << std::endl;
          d_quantEngine->addLemma(eq);
          d_quantEngine->setConflict();
          d_consistent_ee = false;
          return false;
        }
      }
    }
  }

  //compute has map
  if( options::termDbMode()==TERM_DB_RELEVANT || options::lteRestrictInstClosure() ){
    d_has_map.clear();
    d_term_elig_eqc.clear();
    eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( ee );
    while( !eqcs_i.isFinished() ){
      TNode r = (*eqcs_i);
      bool addedFirst = false;
      Node first;
      //TODO: ignoring singleton eqc isn't enough, need to ensure eqc are relevant
      eq::EqClassIterator eqc_i = eq::EqClassIterator( r, ee );
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
    for (TheoryId theoryId = THEORY_FIRST; theoryId < THEORY_LAST; ++theoryId) {
      Theory* theory = d_quantEngine->getTheoryEngine()->d_theoryTable[theoryId];
      if (theory && d_quantEngine->getTheoryEngine()->d_logicInfo.isTheoryEnabled(theoryId)) {
        context::CDList<Assertion>::const_iterator it = theory->facts_begin(), it_end = theory->facts_end();
        for (unsigned i = 0; it != it_end; ++ it, ++i) {
          if( (*it).assertion.getKind()!=INST_CLOSURE ){
            setHasTerm( (*it).assertion );
          }
        }
      }
    }
  }
  //explicitly add inst closure terms to the equality engine to ensure only EE terms are indexed
  for (const Node& n : d_iclosure_processed)
  {
    if( !ee->hasTerm( n ) ){
      ee->addTerm( n );
    }
  }

  if( options::ufHo() && options::hoMergeTermDb() ){
    Trace("quant-ho") << "TermDb::reset : compute equal functions..." << std::endl;
    // build operator representative map
    d_ho_op_rep.clear();
    d_ho_op_slaves.clear();
    eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( ee );
    while( !eqcs_i.isFinished() ){
      TNode r = (*eqcs_i);
      if( r.getType().isFunction() ){
        Trace("quant-ho") << "  process function eqc " << r << std::endl;
        Node first;
        eq::EqClassIterator eqc_i = eq::EqClassIterator( r, ee );
        while( !eqc_i.isFinished() ){
          TNode n = (*eqc_i);
          Node n_use;
          if (n.isVar())
          {
            n_use = n;
          }
          else
          {
            // use its purified variable, if it exists
            std::map<Node, Node>::iterator itp = d_ho_fun_op_purify.find(n);
            if (itp != d_ho_fun_op_purify.end())
            {
              n_use = itp->second;
            }
          }
          Trace("quant-ho") << "  - process " << n_use << ", from " << n
                            << std::endl;
          if (!n_use.isNull() && d_op_map.find(n_use) != d_op_map.end())
          {
            if (first.isNull())
            {
              first = n_use;
              d_ho_op_rep[n_use] = n_use;
            }
            else
            {
              Trace("quant-ho") << "  have : " << n_use << " == " << first
                                << ", type = " << n_use.getType() << std::endl;
              d_ho_op_rep[n_use] = first;
              d_ho_op_slaves[first].push_back(n_use);
            }
          }
          ++eqc_i;
        }
      }
      ++eqcs_i;
    }
    Trace("quant-ho") << "...finished compute equal functions." << std::endl;
  }

/*
  //rebuild d_func/pred_map_trie for each operation, this will calculate all congruent terms
  for( std::map< Node, std::vector< Node > >::iterator it = d_op_map.begin(); it != d_op_map.end(); ++it ){
    computeUfTerms( it->first );
    if( !d_consistent_ee ){
      return false;
    }
  }
*/  
  return true;
}

TNodeTrie* TermDb::getTermArgTrie(Node f)
{
  if( options::ufHo() ){
    f = getOperatorRepresentative( f );
  }
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
  if( options::ufHo() ){
    f = getOperatorRepresentative( f );
  }
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
  if( options::ufHo() ){
    f = getOperatorRepresentative( f );
  }
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
  if( options::ufHo() ){
    f = getOperatorRepresentative( f );
  }
  computeUfTerms( f );
  return d_func_map_trie[f].existsTerm( args );
}

Node TermDb::getHoTypeMatchPredicate(TypeNode tn)
{
  std::map<TypeNode, Node>::iterator ithp = d_ho_type_match_pred.find(tn);
  if (ithp != d_ho_type_match_pred.end())
  {
    return ithp->second;
  }
  NodeManager* nm = NodeManager::currentNM();
  TypeNode ptn = nm->mkFunctionType(tn, nm->booleanType());
  Node k = nm->mkSkolem("U", ptn, "predicate to force higher-order types");
  d_ho_type_match_pred[tn] = k;
  return k;
}

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
