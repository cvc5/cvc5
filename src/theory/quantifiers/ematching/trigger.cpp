/*********************                                                        */
/*! \file trigger.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of trigger class
 **/

#include "theory/quantifiers/ematching/trigger.h"

#include "expr/node_algorithm.h"
#include "theory/arith/arith_msum.h"
#include "theory/quantifiers/ematching/candidate_generator.h"
#include "theory/quantifiers/ematching/ho_trigger.h"
#include "theory/quantifiers/ematching/inst_match_generator.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"
#include "theory/uf/equality_engine.h"
#include "util/hash.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace inst {

void TriggerTermInfo::init( Node q, Node n, int reqPol, Node reqPolEq ){
  if( d_fv.empty() ){
    quantifiers::TermUtil::computeInstConstContainsForQuant(q, n, d_fv);
  }
  if( d_reqPol==0 ){
    d_reqPol = reqPol;
    d_reqPolEq = reqPolEq;
  }else{
    //determined a ground (dis)equality must hold or else q is a tautology?
  }
  d_weight = Trigger::getTriggerWeight(n);
}

/** trigger class constructor */
Trigger::Trigger(QuantifiersEngine* qe, Node q, std::vector<Node>& nodes)
    : d_quantEngine(qe), d_quant(q)
{
  d_nodes.insert( d_nodes.begin(), nodes.begin(), nodes.end() );
  Trace("trigger") << "Trigger for " << q << ": " << std::endl;
  for( unsigned i=0; i<d_nodes.size(); i++ ){
    Trace("trigger") << "   " << d_nodes[i] << std::endl;
  }
  if( d_nodes.size()==1 ){
    if( isSimpleTrigger( d_nodes[0] ) ){
      d_mg = new InstMatchGeneratorSimple(q, d_nodes[0], qe);
    }else{
      d_mg = InstMatchGenerator::mkInstMatchGenerator(q, d_nodes[0], qe);
    }
  }else{
    if( options::multiTriggerCache() ){
      d_mg = new InstMatchGeneratorMulti(q, d_nodes, qe);
    }else{
      d_mg = InstMatchGenerator::mkInstMatchGeneratorMulti(q, d_nodes, qe);
    }
  }
  if( d_nodes.size()==1 ){
    if( isSimpleTrigger( d_nodes[0] ) ){
      ++(qe->d_statistics.d_triggers);
    }else{
      ++(qe->d_statistics.d_simple_triggers);
    }
  }else{
    Trace("multi-trigger") << "Trigger for " << q << ": " << std::endl;
    for( unsigned i=0; i<d_nodes.size(); i++ ){
      Trace("multi-trigger") << "   " << d_nodes[i] << std::endl;
    }
    ++(qe->d_statistics.d_multi_triggers);
  }

  // Notice() << "Trigger : " << (*this) << "  for " << q << std::endl;
  Trace("trigger-debug") << "Finished making trigger." << std::endl;
}

Trigger::~Trigger() {
  delete d_mg;
}

void Trigger::resetInstantiationRound(){
  d_mg->resetInstantiationRound( d_quantEngine );
}

void Trigger::reset( Node eqc ){
  d_mg->reset( eqc, d_quantEngine );
}

Node Trigger::getInstPattern(){
  return NodeManager::currentNM()->mkNode( INST_PATTERN, d_nodes );
}

int Trigger::addInstantiations()
{
  int addedLemmas = d_mg->addInstantiations(d_quant, d_quantEngine, this);
  if( addedLemmas>0 ){
    if (Debug.isOn("inst-trigger"))
    {
      Debug("inst-trigger") << "Added " << addedLemmas
                            << " lemmas, trigger was ";
      for (unsigned i = 0; i < d_nodes.size(); i++)
      {
        Debug("inst-trigger") << d_nodes[i] << " ";
      }
      Debug("inst-trigger") << std::endl;
    }
  }
  return addedLemmas;
}

bool Trigger::sendInstantiation(InstMatch& m)
{
  return d_quantEngine->getInstantiate()->addInstantiation(d_quant, m);
}

bool Trigger::mkTriggerTerms( Node q, std::vector< Node >& nodes, unsigned n_vars, std::vector< Node >& trNodes ) {
  //only take nodes that contribute variables to the trigger when added
  std::vector< Node > temp;
  temp.insert( temp.begin(), nodes.begin(), nodes.end() );
  std::map< Node, bool > vars;
  std::map< Node, std::vector< Node > > patterns;
  size_t varCount = 0;
  std::map< Node, std::vector< Node > > varContains;
  for (const Node& pat : temp)
  {
    quantifiers::TermUtil::computeInstConstContainsForQuant(
        q, pat, varContains[pat]);
  }
  for( unsigned i=0; i<temp.size(); i++ ){
    bool foundVar = false;
    for( unsigned j=0; j<varContains[ temp[i] ].size(); j++ ){
      Node v = varContains[ temp[i] ][j];
      Assert(quantifiers::TermUtil::getInstConstAttr(v) == q);
      if( vars.find( v )==vars.end() ){
        varCount++;
        vars[ v ] = true;
        foundVar = true;
      }
    }
    if( foundVar ){
      trNodes.push_back( temp[i] );
      for( unsigned j=0; j<varContains[ temp[i] ].size(); j++ ){
        Node v = varContains[ temp[i] ][j];
        patterns[ v ].push_back( temp[i] );
      }
    }
    if( varCount==n_vars ){
      break;
    }
  }
  if( varCount<n_vars ){
    Trace("trigger-debug") << "Don't consider trigger since it does not contain specified number of variables." << std::endl;
    for( unsigned i=0; i<nodes.size(); i++) {
      Trace("trigger-debug") << nodes[i] << " ";
    }
    Trace("trigger-debug") << std::endl;

    //do not generate multi-trigger if it does not contain all variables
    return false;
  }else{
    //now, minimize the trigger
    for( unsigned i=0; i<trNodes.size(); i++ ){
      bool keepPattern = false;
      Node n = trNodes[i];
      for( unsigned j=0; j<varContains[ n ].size(); j++ ){
        Node v = varContains[ n ][j];
        if( patterns[v].size()==1 ){
          keepPattern = true;
          break;
        }
      }
      if( !keepPattern ){
        //remove from pattern vector
        for( unsigned j=0; j<varContains[ n ].size(); j++ ){
          Node v = varContains[ n ][j];
          for( unsigned k=0; k<patterns[v].size(); k++ ){
            if( patterns[v][k]==n ){
              patterns[v].erase( patterns[v].begin() + k, patterns[v].begin() + k + 1 );
              break;
            }
          }
        }
        //remove from trigger nodes
        trNodes.erase( trNodes.begin() + i, trNodes.begin() + i + 1 );
        i--;
      }
    }
  }
  return true;
}

Trigger* Trigger::mkTrigger( QuantifiersEngine* qe, Node f, std::vector< Node >& nodes, bool keepAll, int trOption, unsigned use_n_vars ){
  std::vector< Node > trNodes;
  if( !keepAll ){
    unsigned n_vars = use_n_vars==0 ? f[0].getNumChildren() : use_n_vars;
    if( !mkTriggerTerms( f, nodes, n_vars, trNodes ) ){
      return NULL;
    }
  }else{
    trNodes.insert( trNodes.begin(), nodes.begin(), nodes.end() );
  }

  //check for duplicate?
  if( trOption!=TR_MAKE_NEW ){
    Trigger* t = qe->getTriggerDatabase()->getTrigger( trNodes );
    if( t ){
      if( trOption==TR_GET_OLD ){
        //just return old trigger
        return t;
      }else{
        return NULL;
      }
    }
  }

  // check if higher-order
  Trace("trigger-debug") << "Collect higher-order variable triggers..."
                         << std::endl;
  std::map<Node, std::vector<Node> > ho_apps;
  HigherOrderTrigger::collectHoVarApplyTerms(f, trNodes, ho_apps);
  Trace("trigger-debug") << "...got " << ho_apps.size()
                         << " higher-order applications." << std::endl;
  Trigger* t;
  if (!ho_apps.empty())
  {
    t = new HigherOrderTrigger(qe, f, trNodes, ho_apps);
  }
  else
  {
    t = new Trigger(qe, f, trNodes);
  }

  qe->getTriggerDatabase()->addTrigger( trNodes, t );
  return t;
}

Trigger* Trigger::mkTrigger( QuantifiersEngine* qe, Node f, Node n, bool keepAll, int trOption, unsigned use_n_vars ){
  std::vector< Node > nodes;
  nodes.push_back( n );
  return mkTrigger( qe, f, nodes, keepAll, trOption, use_n_vars );
}

bool Trigger::isUsable( Node n, Node q ){
  if( quantifiers::TermUtil::getInstConstAttr(n)==q ){
    if( isAtomicTrigger( n ) ){
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        if( !isUsable( n[i], q ) ){
          return false;
        }
      }
      return true;
    }else if( n.getKind()==INST_CONSTANT ){
      return true;
    }else{
      std::map< Node, Node > coeffs;
      if (options::purifyTriggers())
      {
        Node x = getInversionVariable( n );
        if( !x.isNull() ){
          return true;
        }
      }
    }
    return false;
  }else{
    return true;
  }
}

Node Trigger::getIsUsableEq( Node q, Node n ) {
  Assert(isRelationalTrigger(n));
  for( unsigned i=0; i<2; i++) {
    if( isUsableEqTerms( q, n[i], n[1-i] ) ){
      if( i==1 && n.getKind()==EQUAL && !quantifiers::TermUtil::hasInstConstAttr(n[0]) ){
        return NodeManager::currentNM()->mkNode( n.getKind(), n[1], n[0] );  
      }else{
        return n;
      }
    }
  }
  return Node::null();
}

bool Trigger::isUsableEqTerms( Node q, Node n1, Node n2 ) {
  if( n1.getKind()==INST_CONSTANT ){
    if( options::relationalTriggers() ){
      Node q1 = quantifiers::TermUtil::getInstConstAttr(n1);
      if (q1 != q)
      {
        // x is a variable from another quantified formula, fail
        return false;
      }
      Node q2 = quantifiers::TermUtil::getInstConstAttr(n2);
      if (q2.isNull())
      {
        // x = c
        return true;
      }
      if (n2.getKind() == INST_CONSTANT && q2 == q)
      {
        // x = y
        return true;
      }
      // we dont check x = f(y), which is handled symmetrically below
      // when n1 and n2 are swapped
    }
  }else if( isUsableAtomicTrigger( n1, q ) ){
    if (options::relationalTriggers() && n2.getKind() == INST_CONSTANT
        && quantifiers::TermUtil::getInstConstAttr(n2) == q
        && !expr::hasSubterm(n1, n2))
    {
      // f(x) = y
      return true;
    }
    else if (!quantifiers::TermUtil::hasInstConstAttr(n2))
    {
      // f(x) = c
      return true;
    }
  }
  return false;
}

Node Trigger::getIsUsableTrigger( Node n, Node q ) {
  bool pol = true;
  Trace("trigger-debug") << "Is " << n << " a usable trigger?" << std::endl;
  if( n.getKind()==NOT ){
    pol = !pol;
    n = n[0];
  }
  if( n.getKind()==INST_CONSTANT ){
    return pol ? n : NodeManager::currentNM()->mkNode( EQUAL, n, NodeManager::currentNM()->mkConst( true ) ).notNode();
  }else if( isRelationalTrigger( n ) ){
    Node rtr = getIsUsableEq( q, n );
    if( rtr.isNull() && n[0].getType().isReal() ){
      //try to solve relation
      std::map< Node, Node > m;
      if (ArithMSum::getMonomialSumLit(n, m))
      {
        for( std::map< Node, Node >::iterator it = m.begin(); it!=m.end(); ++it ){
          bool trySolve = false;
          if( !it->first.isNull() ){
            if( it->first.getKind()==INST_CONSTANT ){
              trySolve = options::relationalTriggers();
            }else if( isUsableTrigger( it->first, q ) ){
              trySolve = true;
            }
          }
          if( trySolve ){
            Trace("trigger-debug") << "Try to solve for " << it->first << std::endl;
            Node veq;
            if (ArithMSum::isolate(it->first, m, veq, n.getKind()) != 0)
            {
              rtr = getIsUsableEq( q, veq );
            }
            //either all solves will succeed or all solves will fail
            break;
          }
        }
      }
    }
    if( !rtr.isNull() ){
      Trace("relational-trigger") << "Relational trigger : " << std::endl;
      Trace("relational-trigger") << "    " << rtr << " (from " << n << ")" << std::endl;
      Trace("relational-trigger") << "    in quantifier " << q << std::endl;
      Node rtr2 = pol ? rtr : rtr.negate();
      Trace("relational-trigger") << "    return : " << rtr2 << std::endl;
      return rtr2;
    }
  }else{
    Trace("trigger-debug") << n << " usable : " << ( quantifiers::TermUtil::getInstConstAttr(n)==q ) << " " << isAtomicTrigger( n ) << " " << isUsable( n, q ) << std::endl;
    if( isUsableAtomicTrigger( n, q ) ){
      return pol ? n : NodeManager::currentNM()->mkNode( EQUAL, n, NodeManager::currentNM()->mkConst( true ) ).notNode();
    }
  }
  return Node::null();
}

bool Trigger::isUsableAtomicTrigger( Node n, Node q ) {
  return quantifiers::TermUtil::getInstConstAttr( n )==q && isAtomicTrigger( n ) && isUsable( n, q );
}

bool Trigger::isUsableTrigger( Node n, Node q ){
  Node nu = getIsUsableTrigger( n, q );
  return !nu.isNull();
}

bool Trigger::isAtomicTrigger( Node n ){
  return isAtomicTriggerKind( n.getKind() );
}

bool Trigger::isAtomicTriggerKind( Kind k ) {
  return k == APPLY_UF || k == SELECT || k == STORE || k == APPLY_CONSTRUCTOR
         || k == APPLY_SELECTOR_TOTAL || k == APPLY_TESTER || k == UNION
         || k == INTERSECTION || k == SUBSET || k == SETMINUS || k == MEMBER
         || k == SINGLETON || k == SEP_PTO || k == BITVECTOR_TO_NAT
         || k == INT_TO_BITVECTOR || k == HO_APPLY;
}

bool Trigger::isRelationalTrigger( Node n ) {
  return isRelationalTriggerKind( n.getKind() );
}

bool Trigger::isRelationalTriggerKind( Kind k ) {
  return k==EQUAL || k==GEQ;
}

bool Trigger::isSimpleTrigger( Node n ){
  Node t = n.getKind()==NOT ? n[0] : n;
  if( t.getKind()==EQUAL ){
    if( !quantifiers::TermUtil::hasInstConstAttr( t[1] ) ){
      t = t[0];
    }
  }
  if( isAtomicTrigger( t ) ){
    for( unsigned i=0; i<t.getNumChildren(); i++ ){
      if( t[i].getKind()!=INST_CONSTANT && quantifiers::TermUtil::hasInstConstAttr(t[i]) ){
        return false;
      }
    }
    if( options::purifyDtTriggers() && t.getKind()==APPLY_SELECTOR_TOTAL ){
      return false;
    }
    if (t.getKind() == HO_APPLY && t[0].getKind() == INST_CONSTANT)
    {
      return false;
    }
    return true;
  }else{
    return false;
  }
}

//store triggers in reqPol, indicating their polarity (if any) they must appear to falsify the quantified formula
void Trigger::collectPatTerms2(Node q,
                               Node n,
                               std::map<Node, std::vector<Node> >& visited,
                               std::map<Node, TriggerTermInfo>& tinfo,
                               options::TriggerSelMode tstrt,
                               std::vector<Node>& exclude,
                               std::vector<Node>& added,
                               bool pol,
                               bool hasPol,
                               bool epol,
                               bool hasEPol,
                               bool knowIsUsable)
{
  std::map< Node, std::vector< Node > >::iterator itv = visited.find( n );
  if( itv==visited.end() ){
    visited[ n ].clear();
    Trace("auto-gen-trigger-debug2") << "Collect pat terms " << n << " " << pol << " " << hasPol << " " << epol << " " << hasEPol << std::endl;
    if( n.getKind()!=FORALL && n.getKind()!=INST_CONSTANT ){
      Node nu;
      bool nu_single = false;
      if( knowIsUsable ){
        nu = n;
      }else if( n.getKind()!=NOT && std::find( exclude.begin(), exclude.end(), n )==exclude.end() ){
        nu = getIsUsableTrigger( n, q );
        if( !nu.isNull() && nu!=n ){
          collectPatTerms2( q, nu, visited, tinfo, tstrt, exclude, added, pol, hasPol, epol, hasEPol, true );
          // copy to n
          visited[n].insert( visited[n].end(), added.begin(), added.end() );
          return;
        }
      }
      if( !nu.isNull() ){
        Assert(nu == n);
        Assert(nu.getKind() != NOT);
        Trace("auto-gen-trigger-debug2") << "...found usable trigger : " << nu << std::endl;
        Node reqEq;
        if( nu.getKind()==EQUAL ){
          if( isAtomicTrigger( nu[0] ) && !quantifiers::TermUtil::hasInstConstAttr(nu[1]) ){
            if( hasPol ){
              reqEq = nu[1];
            }
            nu = nu[0];
          }
        }
        Assert(reqEq.isNull()
               || !quantifiers::TermUtil::hasInstConstAttr(reqEq));
        Assert(isUsableTrigger(nu, q));
        //tinfo.find( nu )==tinfo.end()
        Trace("auto-gen-trigger-debug2") << "...add usable trigger : " << nu << std::endl;
        tinfo[ nu ].init( q, nu, hasEPol ? ( epol ? 1 : -1 ) : 0, reqEq );
        nu_single = tinfo[ nu ].d_fv.size()==q[0].getNumChildren();
      }
      Node nrec = nu.isNull() ? n : nu;
      std::vector< Node > added2;
      for( unsigned i=0; i<nrec.getNumChildren(); i++ ){
        bool newHasPol, newPol;
        bool newHasEPol, newEPol;
        QuantPhaseReq::getPolarity( nrec, i, hasPol, pol, newHasPol, newPol );
        QuantPhaseReq::getEntailPolarity( nrec, i, hasEPol, epol, newHasEPol, newEPol );
        collectPatTerms2( q, nrec[i], visited, tinfo, tstrt, exclude, added2, newPol, newHasPol, newEPol, newHasEPol );
      }
      // if this is not a usable trigger, don't worry about caching the results, since triggers do not contain non-usable subterms
      if( !nu.isNull() ){
        bool rm_nu = false;
        for( unsigned i=0; i<added2.size(); i++ ){
          Trace("auto-gen-trigger-debug2") << "..." << nu << " added child " << i << " : " << added2[i] << std::endl;
          Assert(added2[i] != nu);
          // if child was not already removed
          if( tinfo.find( added2[i] )!=tinfo.end() ){
            if (tstrt == options::TriggerSelMode::MAX
                || (tstrt == options::TriggerSelMode::MIN_SINGLE_MAX
                    && !nu_single))
            {
              // discard all subterms
              // do not remove if it has smaller weight
              if (tinfo[nu].d_weight <= tinfo[added2[i]].d_weight)
              {
                Trace("auto-gen-trigger-debug2")
                    << "......remove it." << std::endl;
                visited[added2[i]].clear();
                tinfo.erase(added2[i]);
              }
            }
            else
            {
              if( tinfo[ nu ].d_fv.size()==tinfo[ added2[i] ].d_fv.size() ){
                if (tinfo[nu].d_weight >= tinfo[added2[i]].d_weight)
                {
                  // discard if we added a subterm as a trigger with all
                  // variables that nu has
                  Trace("auto-gen-trigger-debug2")
                      << "......subsumes parent " << tinfo[nu].d_weight << " "
                      << tinfo[added2[i]].d_weight << "." << std::endl;
                  rm_nu = true;
                }
              }
              if( std::find( added.begin(), added.end(), added2[i] )==added.end() ){
                added.push_back( added2[i] );
              }
            }
          }
        }
        if (rm_nu
            && (tstrt == options::TriggerSelMode::MIN
                || (tstrt == options::TriggerSelMode::MIN_SINGLE_ALL
                    && nu_single)))
        {
          tinfo.erase( nu );
        }
        else
        {
          if( std::find( added.begin(), added.end(), nu )==added.end() ){
            added.push_back( nu );
          }
        }
        visited[n].insert( visited[n].end(), added.begin(), added.end() );
      }
    }
  }else{
    for( unsigned i=0; i<itv->second.size(); ++i ){
      Node t = itv->second[i];
      if( std::find( added.begin(), added.end(), t )==added.end() ){
        added.push_back( t );
      }
    }
  }
}

bool Trigger::isPureTheoryTrigger( Node n ) {
  if( n.getKind()==APPLY_UF || n.getKind()==VARIABLE || n.getKind()==SKOLEM ){  //|| !quantifiers::TermUtil::hasInstConstAttr( n ) ){
    return false;
  }else{
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( !isPureTheoryTrigger( n[i] ) ){
        return false;
      }
    }
    return true;
  }
}

int Trigger::getTriggerWeight( Node n ) {
  if (n.getKind() == APPLY_UF)
  {
    return 0;
  }
  if (isAtomicTrigger(n))
  {
    return 1;
  }
  return 2;
}

bool Trigger::isLocalTheoryExt( Node n, std::vector< Node >& vars, std::vector< Node >& patTerms ) {
  if( !n.getType().isBoolean() && n.getKind()==APPLY_UF ){
    if( std::find( patTerms.begin(), patTerms.end(), n )==patTerms.end() ){
      bool hasVar = false;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        if( n[i].getKind()==INST_CONSTANT ){
          hasVar = true;
          if( std::find( vars.begin(), vars.end(), n[i] )==vars.end() ){
            vars.push_back( n[i] );
          }else{
            //do not allow duplicate variables
            return false;
          }
        }else{
          //do not allow nested function applications
          return false;
        }
      }
      if( hasVar ){
        patTerms.push_back( n );
      }
    }
  }else{
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( !isLocalTheoryExt( n[i], vars, patTerms ) ){
        return false;
      }
    }
  }
  return true;
}

void Trigger::collectPatTerms(Node q,
                              Node n,
                              std::vector<Node>& patTerms,
                              options::TriggerSelMode tstrt,
                              std::vector<Node>& exclude,
                              std::map<Node, TriggerTermInfo>& tinfo,
                              bool filterInst)
{
  std::map< Node, std::vector< Node > > visited;
  if( filterInst ){
    //immediately do not consider any term t for which another term is an instance of t
    std::vector< Node > patTerms2;
    std::map< Node, TriggerTermInfo > tinfo2;
    collectPatTerms(
        q, n, patTerms2, options::TriggerSelMode::ALL, exclude, tinfo2, false);
    std::vector< Node > temp;
    temp.insert( temp.begin(), patTerms2.begin(), patTerms2.end() );
    filterTriggerInstances(temp);
    if (Trace.isOn("trigger-filter-instance"))
    {
      if (temp.size() != patTerms2.size())
      {
        Trace("trigger-filter-instance") << "Filtered an instance: "
                                         << std::endl;
        Trace("trigger-filter-instance") << "Old: ";
        for (unsigned i = 0; i < patTerms2.size(); i++)
        {
          Trace("trigger-filter-instance") << patTerms2[i] << " ";
        }
        Trace("trigger-filter-instance") << std::endl << "New: ";
        for (unsigned i = 0; i < temp.size(); i++)
        {
          Trace("trigger-filter-instance") << temp[i] << " ";
        }
        Trace("trigger-filter-instance") << std::endl;
      }
    }
    if (tstrt == options::TriggerSelMode::ALL)
    {
      for( unsigned i=0; i<temp.size(); i++ ){
        //copy information
        tinfo[temp[i]].d_fv.insert( tinfo[temp[i]].d_fv.end(), tinfo2[temp[i]].d_fv.begin(), tinfo2[temp[i]].d_fv.end() );
        tinfo[temp[i]].d_reqPol = tinfo2[temp[i]].d_reqPol;
        tinfo[temp[i]].d_reqPolEq = tinfo2[temp[i]].d_reqPolEq;
        patTerms.push_back( temp[i] );
      }
      return;
    }
    else
    {
      //do not consider terms that have instances
      for( unsigned i=0; i<patTerms2.size(); i++ ){
        if( std::find( temp.begin(), temp.end(), patTerms2[i] )==temp.end() ){
          visited[ patTerms2[i] ].clear();
        }
      }
    }
  }
  std::vector< Node > added;
  collectPatTerms2( q, n, visited, tinfo, tstrt, exclude, added, true, true, false, true );
  for( std::map< Node, TriggerTermInfo >::iterator it = tinfo.begin(); it != tinfo.end(); ++it ){
    patTerms.push_back( it->first );
  }
}

int Trigger::isTriggerInstanceOf(Node n1,
                                 Node n2,
                                 std::vector<Node>& fv1,
                                 std::vector<Node>& fv2)
{
  Assert(n1 != n2);
  int status = 0;
  std::unordered_set<TNode, TNodeHashFunction> subs_vars;
  std::unordered_set<std::pair<TNode, TNode>,
                     PairHashFunction<TNode,
                                      TNode,
                                      TNodeHashFunction,
                                      TNodeHashFunction> >
      visited;
  std::vector<std::pair<TNode, TNode> > visit;
  std::pair<TNode, TNode> cur;
  TNode cur1;
  TNode cur2;
  visit.push_back(std::pair<TNode, TNode>(n1, n2));
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      cur1 = cur.first;
      cur2 = cur.second;
      Assert(cur1 != cur2);
      // recurse if they have the same operator
      if (cur1.hasOperator() && cur2.hasOperator()
          && cur1.getNumChildren() == cur2.getNumChildren()
          && cur1.getOperator() == cur2.getOperator()
          && cur1.getOperator().getKind()!=INST_CONSTANT)
      {
        visit.push_back(std::pair<TNode, TNode>(cur1, cur2));
        for (unsigned i = 0, size = cur1.getNumChildren(); i < size; i++)
        {
          if (cur1[i] != cur2[i])
          {
            visit.push_back(std::pair<TNode, TNode>(cur1[i], cur2[i]));
          }
          else if (cur1[i].getKind() == INST_CONSTANT)
          {
            if (subs_vars.find(cur1[i]) != subs_vars.end())
            {
              return 0;
            }
            // the variable must map to itself in the substitution
            subs_vars.insert(cur1[i]);
          }
        }
      }
      else
      {
        bool success = false;
        // check if we are in a unifiable instance case
        // must be only this case
        for (unsigned r = 0; r < 2; r++)
        {
          if (status == 0 || ((status == 1) == (r == 0)))
          {
            TNode curi = r == 0 ? cur1 : cur2;
            if (curi.getKind() == INST_CONSTANT
                && subs_vars.find(curi) == subs_vars.end())
            {
              TNode curj = r == 0 ? cur2 : cur1;
              // RHS must be a simple trigger
              if (getTriggerWeight(curj) == 0)
              {
                // must occur in the free variables in the other
                std::vector<Node>& free_vars = r == 0 ? fv2 : fv1;
                if (std::find(free_vars.begin(), free_vars.end(), curi)
                    != free_vars.end())
                {
                  status = r == 0 ? 1 : -1;
                  subs_vars.insert(curi);
                  success = true;
                  break;
                }
              }
            }
          }
        }
        if (!success)
        {
          return 0;
        }
      }
    }
  } while (!visit.empty());
  return status;
}

void Trigger::filterTriggerInstances(std::vector<Node>& nodes)
{
  std::map<unsigned, std::vector<Node> > fvs;
  for (unsigned i = 0, size = nodes.size(); i < size; i++)
  {
    quantifiers::TermUtil::computeInstConstContains(nodes[i], fvs[i]);
  }
  std::vector<bool> active;
  active.resize(nodes.size(), true);
  for (unsigned i = 0, size = nodes.size(); i < size; i++)
  {
    std::vector<Node>& fvsi = fvs[i];
    if (active[i])
    {
      for (unsigned j = i + 1, size2 = nodes.size(); j < size2; j++)
      {
        if (active[j])
        {
          int result = isTriggerInstanceOf(nodes[i], nodes[j], fvsi, fvs[j]);
          if (result == 1)
          {
            Trace("filter-instances") << nodes[j] << " is an instance of "
                                      << nodes[i] << std::endl;
            active[i] = false;
            break;
          }
          else if (result == -1)
          {
            Trace("filter-instances") << nodes[i] << " is an instance of "
                                      << nodes[j] << std::endl;
            active[j] = false;
          }
        }
      }
    }
  }
  std::vector<Node> temp;
  for (unsigned i = 0; i < nodes.size(); i++)
  {
    if (active[i])
    {
      temp.push_back(nodes[i]);
    }
  }
  nodes.clear();
  nodes.insert(nodes.begin(), temp.begin(), temp.end());
}

Node Trigger::getInversionVariable( Node n ) {
  if( n.getKind()==INST_CONSTANT ){
    return n;
  }else if( n.getKind()==PLUS || n.getKind()==MULT ){
    Node ret;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( quantifiers::TermUtil::hasInstConstAttr(n[i]) ){
        if( ret.isNull() ){
          ret = getInversionVariable( n[i] );
          if( ret.isNull() ){
            Trace("var-trigger-debug") << "No : multiple variables " << n << std::endl;
            return Node::null();
          }
        }else{
          return Node::null();
        }
      }else if( n.getKind()==MULT ){
        if( !n[i].isConst() ){
          Trace("var-trigger-debug") << "No : non-linear coefficient " << n << std::endl;
          return Node::null();
        }
        /*
        else if( n.getType().isInteger() ){
          Rational r = n[i].getConst<Rational>();
          if( r!=Rational(-1) && r!=Rational(1) ){
            Trace("var-trigger-debug") << "No : not integer coefficient " << n << std::endl;
            return Node::null();
          }
        }
        */
      }
    }
    return ret;
  }else{
    Trace("var-trigger-debug") << "No : unsupported operator " << n << "." << std::endl;
  }
  return Node::null();
}

Node Trigger::getInversion( Node n, Node x ) {
  if( n.getKind()==INST_CONSTANT ){
    return x;
  }else if( n.getKind()==PLUS || n.getKind()==MULT ){
    int cindex = -1;
    bool cindexSet = false;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( !quantifiers::TermUtil::hasInstConstAttr(n[i]) ){
        if( n.getKind()==PLUS ){
          x = NodeManager::currentNM()->mkNode( MINUS, x, n[i] );
        }else if( n.getKind()==MULT ){
          Assert(n[i].isConst());
          if( x.getType().isInteger() ){
            Node coeff = NodeManager::currentNM()->mkConst( n[i].getConst<Rational>().abs() );
            if( !n[i].getConst<Rational>().abs().isOne() ){
              x = NodeManager::currentNM()->mkNode( INTS_DIVISION_TOTAL, x, coeff );
            }
            if( n[i].getConst<Rational>().sgn()<0 ){
              x = NodeManager::currentNM()->mkNode( UMINUS, x );
            }
          }else{
            Node coeff = NodeManager::currentNM()->mkConst( Rational(1) / n[i].getConst<Rational>() );
            x = NodeManager::currentNM()->mkNode( MULT, x, coeff );
          }
        }
        x = Rewriter::rewrite( x );
      }else{
        Assert(!cindexSet);
        cindex = i;
        cindexSet = true;
      }
    }
    if (cindexSet)
    {
      return getInversion(n[cindex], x);
    }
  }
  return Node::null();
}

void Trigger::getTriggerVariables(Node n, Node q, std::vector<Node>& t_vars)
{
  std::vector< Node > patTerms;
  std::map< Node, TriggerTermInfo > tinfo;
  // collect all patterns from n
  std::vector< Node > exclude;
  collectPatTerms(q, n, patTerms, options::TriggerSelMode::ALL, exclude, tinfo);
  //collect all variables from all patterns in patTerms, add to t_vars
  for (const Node& pat : patTerms)
  {
    quantifiers::TermUtil::computeInstConstContainsForQuant(q, pat, t_vars);
  }
}

int Trigger::getActiveScore() {
  return d_mg->getActiveScore( d_quantEngine );
}

TriggerTrie::TriggerTrie()
{}

TriggerTrie::~TriggerTrie() {
  for(std::map< TNode, TriggerTrie* >::iterator i = d_children.begin(), iend = d_children.end();
      i != iend; ++i) {
    TriggerTrie* current = (*i).second;
    delete current;
  }
  d_children.clear();

  for( unsigned i=0; i<d_tr.size(); i++ ){
    delete d_tr[i];
  }
}

inst::Trigger* TriggerTrie::getTrigger(std::vector<Node>& nodes)
{
  std::vector<Node> temp;
  temp.insert(temp.begin(), nodes.begin(), nodes.end());
  std::sort(temp.begin(), temp.end());
  TriggerTrie* tt = this;
  for (const Node& n : temp)
  {
    std::map<TNode, TriggerTrie*>::iterator itt = tt->d_children.find(n);
    if (itt == tt->d_children.end())
    {
      return NULL;
    }
    else
    {
      tt = itt->second;
    }
  }
  return tt->d_tr.empty() ? NULL : tt->d_tr[0];
}

void TriggerTrie::addTrigger(std::vector<Node>& nodes, inst::Trigger* t)
{
  std::vector<Node> temp;
  temp.insert(temp.begin(), nodes.begin(), nodes.end());
  std::sort(temp.begin(), temp.end());
  TriggerTrie* tt = this;
  for (const Node& n : temp)
  {
    std::map<TNode, TriggerTrie*>::iterator itt = tt->d_children.find(n);
    if (itt == tt->d_children.end())
    {
      TriggerTrie* ttn = new TriggerTrie;
      tt->d_children[n] = ttn;
      tt = ttn;
    }
    else
    {
      tt = itt->second;
    }
  }
  tt->d_tr.push_back(t);
}

}/* CVC4::theory::inst namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
