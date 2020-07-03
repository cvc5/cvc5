/*********************                                                        */
/*! \file inst_strategy_cegqi.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of counterexample-guided quantifier instantiation strategies
 **/
#include "theory/quantifiers/cegqi/inst_strategy_cegqi.h"

#include "expr/node_algorithm.h"
#include "options/quantifiers_options.h"
#include "smt/term_formula_removal.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/theory_arith.h"
#include "theory/arith/theory_arith_private.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quant_epr.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace quantifiers {

InstRewriterCegqi::InstRewriterCegqi(InstStrategyCegqi* p)
    : InstantiationRewriter(), d_parent(p)
{
}

TrustNode InstRewriterCegqi::rewriteInstantiation(Node q,
                                                  std::vector<Node>& terms,
                                                  Node inst,
                                                  bool doVts)
{
  return d_parent->rewriteInstantiation(q, terms, inst, doVts);
}

InstStrategyCegqi::InstStrategyCegqi(QuantifiersEngine* qe)
    : QuantifiersModule(qe),
      d_irew(new InstRewriterCegqi(this)),
      d_cbqi_set_quant_inactive(false),
      d_incomplete_check(false),
      d_added_cbqi_lemma(qe->getUserContext()),
      d_elim_quants(qe->getSatContext()),
      d_vtsCache(new VtsTermCache(qe)),
      d_bv_invert(nullptr),
      d_nested_qe_waitlist_size(qe->getUserContext()),
      d_nested_qe_waitlist_proc(qe->getUserContext())
{
  d_qid_count = 0;
  d_small_const =
      NodeManager::currentNM()->mkConst(Rational(1) / Rational(1000000));
  d_check_vts_lemma_lc = false;
  if (options::cegqiBv())
  {
    // if doing instantiation for BV, need the inverter class
    d_bv_invert.reset(new quantifiers::BvInverter);
  }
}

InstStrategyCegqi::~InstStrategyCegqi() {}

bool InstStrategyCegqi::needsCheck(Theory::Effort e)
{
  return e>=Theory::EFFORT_LAST_CALL;
}

QuantifiersModule::QEffort InstStrategyCegqi::needsModel(Theory::Effort e)
{
  for( unsigned i=0; i<d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
    Node q = d_quantEngine->getModel()->getAssertedQuantifier( i );
    if( doCbqi( q ) && d_quantEngine->getModel()->isQuantifierActive( q ) ){
      return QEFFORT_STANDARD;
    }
  }
  return QEFFORT_NONE;
}

bool InstStrategyCegqi::registerCbqiLemma(Node q)
{
  if( !hasAddedCbqiLemma( q ) ){
    NodeManager* nm = NodeManager::currentNM();
    d_added_cbqi_lemma.insert( q );
    Trace("cegqi-debug") << "Do cbqi for " << q << std::endl;
    //add cbqi lemma
    //get the counterexample literal
    Node ceLit = getCounterexampleLiteral(q);
    Node ceBody = d_quantEngine->getTermUtil()->getInstConstantBody( q );
    if( !ceBody.isNull() ){
      //add counterexample lemma
      Node lem = NodeManager::currentNM()->mkNode( OR, ceLit.negate(), ceBody.negate() );
      //require any decision on cel to be phase=true
      d_quantEngine->addRequirePhase( ceLit, true );
      Debug("cegqi-debug") << "Require phase " << ceLit << " = true." << std::endl;
      //add counterexample lemma
      lem = Rewriter::rewrite( lem );
      Trace("cegqi-lemma") << "Counterexample lemma : " << lem << std::endl;
      registerCounterexampleLemma( q, lem );
      
      //totality lemmas for EPR
      QuantEPR * qepr = d_quantEngine->getQuantEPR();
      if( qepr!=NULL ){   
        for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
          TypeNode tn = q[0][i].getType();
          if( tn.isSort() ){
            if( qepr->isEPR( tn ) ){
              //add totality lemma
              std::map< TypeNode, std::vector< Node > >::iterator itc = qepr->d_consts.find( tn );
              if( itc!=qepr->d_consts.end() ){
                Assert(!itc->second.empty());
                Node ic = d_quantEngine->getTermUtil()->getInstantiationConstant( q, i );
                std::vector< Node > disj;
                for( unsigned j=0; j<itc->second.size(); j++ ){
                  disj.push_back( ic.eqNode( itc->second[j] ) );
                }
                Node tlem = disj.size()==1 ? disj[0] : NodeManager::currentNM()->mkNode( kind::OR, disj );
                Trace("cegqi-lemma") << "EPR totality lemma : " << tlem << std::endl;
                d_quantEngine->getOutputChannel().lemma( tlem );
              }else{
                Assert(false);
              }                  
            }
          }
        }
      }      
      
      //compute dependencies between quantified formulas
      std::vector<Node> ics;
      TermUtil::computeInstConstContains(q, ics);
      d_parent_quant[q].clear();
      d_children_quant[q].clear();
      std::vector<Node> dep;
      for (const Node& ic : ics)
      {
        Node qi = ic.getAttribute(InstConstantAttribute());
        if (std::find(d_parent_quant[q].begin(), d_parent_quant[q].end(), qi)
            == d_parent_quant[q].end())
        {
          d_parent_quant[q].push_back(qi);
          d_children_quant[qi].push_back(q);
          Assert(hasAddedCbqiLemma(qi));
          Node qicel = getCounterexampleLiteral(qi);
          dep.push_back(qi);
          dep.push_back(qicel);
        }
      }
      if (!dep.empty())
      {
        Node dep_lemma = nm->mkNode(IMPLIES, ceLit, nm->mkNode(AND, dep));
        Trace("cegqi-lemma")
            << "Counterexample dependency lemma : " << dep_lemma << std::endl;
        d_quantEngine->getOutputChannel().lemma(dep_lemma);
      }

      //must register all sub-quantifiers of counterexample lemma, register their lemmas
      std::vector< Node > quants;
      TermUtil::computeQuantContains( lem, quants );
      for( unsigned i=0; i<quants.size(); i++ ){
        if( doCbqi( quants[i] ) ){
          registerCbqiLemma( quants[i] );
        }
        if( options::cegqiNestedQE() ){
          //record these as counterexample quantifiers
          QAttributes qa;
          QuantAttributes::computeQuantAttributes( quants[i], qa );
          if( !qa.d_qid_num.isNull() ){
            d_id_to_ce_quant[ qa.d_qid_num ] = quants[i];
            d_ce_quant_to_id[ quants[i] ] = qa.d_qid_num;
            Trace("cegqi-nqe") << "CE quant id = " << qa.d_qid_num << " is " << quants[i] << std::endl;
          }
        }
      }
    }
    // The decision strategy for this quantified formula ensures that its
    // counterexample literal is decided on first. It is user-context dependent.
    std::map<Node, std::unique_ptr<DecisionStrategy>>::iterator itds =
        d_dstrat.find(q);
    DecisionStrategy* dlds = nullptr;
    if (itds == d_dstrat.end())
    {
      d_dstrat[q].reset(
          new DecisionStrategySingleton("CexLiteral",
                                        ceLit,
                                        d_quantEngine->getSatContext(),
                                        d_quantEngine->getValuation()));
      dlds = d_dstrat[q].get();
    }
    else
    {
      dlds = itds->second.get();
    }
    // it is appended to the list of strategies
    d_quantEngine->getTheoryEngine()->getDecisionManager()->registerStrategy(
        DecisionManager::STRAT_QUANT_CEGQI_FEASIBLE, dlds);
    return true;
  }else{
    return false;
  }
}

void InstStrategyCegqi::reset_round(Theory::Effort effort)
{
  d_cbqi_set_quant_inactive = false;
  d_incomplete_check = false;
  d_active_quant.clear();
  //check if any cbqi lemma has not been added yet
  for( unsigned i=0; i<d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
    Node q = d_quantEngine->getModel()->getAssertedQuantifier( i );
    //it is not active if it corresponds to a rewrite rule: we will process in rewrite engine
    if( doCbqi( q ) ){
      Assert(hasAddedCbqiLemma(q));
      if( d_quantEngine->getModel()->isQuantifierActive( q ) ){
        d_active_quant[q] = true;
        Debug("cegqi-debug") << "Check quantified formula " << q << "..." << std::endl;
        Node cel = getCounterexampleLiteral(q);
        bool value;
        if( d_quantEngine->getValuation().hasSatValue( cel, value ) ){
          Debug("cegqi-debug") << "...CE Literal has value " << value << std::endl;
          if( !value ){
            if( d_quantEngine->getValuation().isDecision( cel ) ){
              Trace("cegqi-warn") << "CBQI WARNING: Bad decision on CE Literal." << std::endl;
            }else{
              Trace("cegqi") << "Inactive : " << q << std::endl;
              d_quantEngine->getModel()->setQuantifierActive( q, false );
              d_cbqi_set_quant_inactive = true;
              d_active_quant.erase( q );
              d_elim_quants.insert( q );
              Trace("cegqi-nqe") << "Inactive, waitlist proc/size = " << d_nested_qe_waitlist_proc[q].get() << "/" << d_nested_qe_waitlist_size[q].get() << std::endl;
              //process from waitlist
              while( d_nested_qe_waitlist_proc[q]<d_nested_qe_waitlist_size[q] ){
                int index = d_nested_qe_waitlist_proc[q];
                Assert(index >= 0);
                Assert(index < (int)d_nested_qe_waitlist[q].size());
                Node nq = d_nested_qe_waitlist[q][index];
                Node nqeqn = doNestedQENode( d_nested_qe_info[nq].d_q, q, nq, d_nested_qe_info[nq].d_inst_terms, d_nested_qe_info[nq].d_doVts );
                Node dqelem = nq.eqNode( nqeqn ); 
                Trace("cegqi-lemma") << "Delayed nested quantifier elimination lemma : " << dqelem << std::endl;
                d_quantEngine->getOutputChannel().lemma( dqelem );
                d_nested_qe_waitlist_proc[q] = index + 1;
              }
            }
          }
        }else{
          Debug("cegqi-debug") << "...CE Literal does not have value " << std::endl;
        }
      }
    }
  }

  //refinement: only consider innermost active quantified formulas
  if( options::cegqiInnermost() ){
    if( !d_children_quant.empty() && !d_active_quant.empty() ){
      Trace("cegqi-debug") << "Find non-innermost quantifiers..." << std::endl;
      std::vector< Node > ninner;
      for( std::map< Node, bool >::iterator it = d_active_quant.begin(); it != d_active_quant.end(); ++it ){
        std::map< Node, std::vector< Node > >::iterator itc = d_children_quant.find( it->first );
        if( itc!=d_children_quant.end() ){
          for( unsigned j=0; j<itc->second.size(); j++ ){
            if( d_active_quant.find( itc->second[j] )!=d_active_quant.end() ){
              Trace("cegqi-debug") << "Do not consider " << it->first << " since it is not innermost (" << itc->second[j] << std::endl;
              ninner.push_back( it->first );
              break;
            }
          }
        }
      } 
      Trace("cegqi-debug") << "Found " << ninner.size() << " non-innermost." << std::endl;
      for( unsigned i=0; i<ninner.size(); i++ ){
        Assert(d_active_quant.find(ninner[i]) != d_active_quant.end());
        d_active_quant.erase( ninner[i] );
      }
      Assert(!d_active_quant.empty());
      Trace("cegqi-debug") << "...done removing." << std::endl;
    }
  }
  d_check_vts_lemma_lc = false;
}

void InstStrategyCegqi::check(Theory::Effort e, QEffort quant_e)
{
  if (quant_e == QEFFORT_STANDARD)
  {
    Assert(!d_quantEngine->inConflict());
    double clSet = 0;
    if( Trace.isOn("cegqi-engine") ){
      clSet = double(clock())/double(CLOCKS_PER_SEC);
      Trace("cegqi-engine") << "---Cbqi Engine Round, effort = " << e << "---" << std::endl;
    }
    unsigned lastWaiting = d_quantEngine->getNumLemmasWaiting();
    for( int ee=0; ee<=1; ee++ ){
      //for( unsigned i=0; i<d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
      //  Node q = d_quantEngine->getModel()->getAssertedQuantifier( i );
      //  if( doCbqi( q ) && d_quantEngine->getModel()->isQuantifierActive( q ) ){
      for( std::map< Node, bool >::iterator it = d_active_quant.begin(); it != d_active_quant.end(); ++it ){
        Node q = it->first;
        Trace("cegqi") << "CBQI : Process quantifier " << q[0] << " at effort " << ee << std::endl;
        if( d_nested_qe.find( q )==d_nested_qe.end() ){
          process( q, e, ee );
          if( d_quantEngine->inConflict() ){
            break;
          }
        }else{
          Trace("cegqi-warn") << "CBQI : Cannot process already eliminated quantified formula " << q << std::endl;
          Assert(false);
        }
      }
      if( d_quantEngine->inConflict() || d_quantEngine->getNumLemmasWaiting()>lastWaiting ){
        break;
      }
    }
    if( Trace.isOn("cegqi-engine") ){
      if( d_quantEngine->getNumLemmasWaiting()>lastWaiting ){
        Trace("cegqi-engine") << "Added lemmas = " << (d_quantEngine->getNumLemmasWaiting()-lastWaiting) << std::endl;
      }
      double clSet2 = double(clock())/double(CLOCKS_PER_SEC);
      Trace("cegqi-engine") << "Finished cbqi engine, time = " << (clSet2-clSet) << std::endl;
    }
  }
}

bool InstStrategyCegqi::checkComplete()
{
  if( ( !options::cegqiSat() && d_cbqi_set_quant_inactive ) || d_incomplete_check ){
    return false;
  }else{
    return true;
  }
}

bool InstStrategyCegqi::checkCompleteFor(Node q)
{
  std::map<Node, CegHandledStatus>::iterator it = d_do_cbqi.find(q);
  if( it!=d_do_cbqi.end() ){
    return it->second != CEG_UNHANDLED;
  }else{
    return false;
  }
}

Node InstStrategyCegqi::getIdMarkedQuantNode(Node n,
                                             std::map<Node, Node>& visited)
{
  std::map< Node, Node >::iterator it = visited.find( n );
  if( it==visited.end() ){
    Node ret = n;
    if( n.getKind()==FORALL ){
      QAttributes qa;
      QuantAttributes::computeQuantAttributes( n, qa );
      if( qa.d_qid_num.isNull() ){
        std::vector< Node > rc;
        rc.push_back( n[0] );
        rc.push_back( getIdMarkedQuantNode( n[1], visited ) );
        Node avar = NodeManager::currentNM()->mkSkolem( "id", NodeManager::currentNM()->booleanType() );
        QuantIdNumAttribute ida;
        avar.setAttribute(ida,d_qid_count);
        d_qid_count++;
        std::vector< Node > iplc;
        iplc.push_back( NodeManager::currentNM()->mkNode( INST_ATTRIBUTE, avar ) );
        if( n.getNumChildren()==3 ){
          for( unsigned i=0; i<n[2].getNumChildren(); i++ ){
            iplc.push_back( n[2][i] );
          }
        }
        rc.push_back( NodeManager::currentNM()->mkNode( INST_PATTERN_LIST, iplc ) );
        ret = NodeManager::currentNM()->mkNode( FORALL, rc );
      }
    }else if( n.getNumChildren()>0 ){
      std::vector< Node > children;
      if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
        children.push_back( n.getOperator() );
      }
      bool childChanged = false;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        Node nc = getIdMarkedQuantNode( n[i], visited );
        childChanged = childChanged || nc!=n[i];
        children.push_back( nc );
      }
      if( childChanged ){
        ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
      }
    }
    visited[n] = ret;
    return ret;
  }else{
    return it->second;
  }
}

void InstStrategyCegqi::checkOwnership(Node q)
{
  if( d_quantEngine->getOwner( q )==NULL && doCbqi( q ) ){
    if (d_do_cbqi[q] == CEG_HANDLED)
    {
      //take full ownership of the quantified formula
      d_quantEngine->setOwner( q, this );
    }
  }
}

void InstStrategyCegqi::preRegisterQuantifier(Node q)
{
  // mark all nested quantifiers with id
  if (options::cegqiNestedQE())
  {
    if( d_quantEngine->getOwner(q)==this )
    {
      std::map<Node, Node> visited;
      Node mq = getIdMarkedQuantNode(q[1], visited);
      if (mq != q[1])
      {
        // do not do cbqi, we are reducing this quantified formula to a marked
        // one
        d_do_cbqi[q] = CEG_UNHANDLED;
        // instead do reduction
        std::vector<Node> qqc;
        qqc.push_back(q[0]);
        qqc.push_back(mq);
        if (q.getNumChildren() == 3)
        {
          qqc.push_back(q[2]);
        }
        Node qq = NodeManager::currentNM()->mkNode(FORALL, qqc);
        Node mlem = NodeManager::currentNM()->mkNode(IMPLIES, q, qq);
        Trace("cegqi-lemma") << "Mark quant id lemma : " << mlem << std::endl;
        d_quantEngine->addLemma(mlem);
      }
    }
  }
  if( doCbqi( q ) ){
    // get the instantiator
    if (options::cegqiPreRegInst())
    {
      getInstantiator(q);
    }
    // register the cbqi lemma
    if( registerCbqiLemma( q ) ){
      Trace("cegqi") << "Registered cbqi lemma for quantifier : " << q << std::endl;
    }
  }
}
TrustNode InstStrategyCegqi::rewriteInstantiation(Node q,
                                                  std::vector<Node>& terms,
                                                  Node inst,
                                                  bool doVts)
{
  Node prevInst = inst;
  if (doVts)
  {
    // do virtual term substitution
    inst = Rewriter::rewrite(inst);
    Trace("quant-vts-debug") << "Rewrite vts symbols in " << inst << std::endl;
    inst = d_vtsCache->rewriteVtsSymbols(inst);
    Trace("quant-vts-debug") << "...got " << inst << std::endl;
  }
  if (options::cegqiNestedQE())
  {
    inst = doNestedQE(q, terms, inst, doVts);
  }
  if (prevInst != inst)
  {
    // not proof producing yet
    return TrustNode::mkTrustRewrite(prevInst, inst, nullptr);
  }
  return TrustNode::null();
}

InstantiationRewriter* InstStrategyCegqi::getInstRewriter() const
{
  return d_irew.get();
}

Node InstStrategyCegqi::doNestedQENode(
    Node q, Node ceq, Node n, std::vector<Node>& inst_terms, bool doVts)
{
  // there is a nested quantified formula (forall y. nq[y,x]) such that 
  //    q is (forall y. nq[y,t]) for ground terms t,
  //    ceq is (forall y. nq[y,e]) for CE variables e.
  // we call this function when we know (forall y. nq[y,e]) is equivalent to quantifier-free formula C[e].
  // in this case, q is equivalent to the quantifier-free formula C[t].
  if( d_nested_qe.find( ceq )==d_nested_qe.end() ){
    d_nested_qe[ceq] = d_quantEngine->getInstantiatedConjunction( ceq );
    Trace("cegqi-nqe") << "CE quantifier elimination : " << std::endl;
    Trace("cegqi-nqe") << "  " << ceq << std::endl; 
    Trace("cegqi-nqe") << "  " << d_nested_qe[ceq] << std::endl;
    //should not contain quantifiers
    Assert(!expr::hasClosure(d_nested_qe[ceq]));
  }
  Assert(d_quantEngine->getTermUtil()->d_inst_constants[q].size()
         == inst_terms.size());
  //replace inst constants with instantiation
  Node ret = d_nested_qe[ceq].substitute( d_quantEngine->getTermUtil()->d_inst_constants[q].begin(),
                                          d_quantEngine->getTermUtil()->d_inst_constants[q].end(),
                                          inst_terms.begin(), inst_terms.end() );
  if( doVts ){
    //do virtual term substitution
    ret = Rewriter::rewrite( ret );
    ret = d_vtsCache->rewriteVtsSymbols(ret);
  }
  Trace("cegqi-nqe") << "Nested quantifier elimination: " << std::endl;
  Trace("cegqi-nqe") << "  " << n << std::endl; 
  Trace("cegqi-nqe") << "  " << ret << std::endl;
  return ret;
}

Node InstStrategyCegqi::doNestedQERec(Node q,
                                      Node n,
                                      std::map<Node, Node>& visited,
                                      std::vector<Node>& inst_terms,
                                      bool doVts)
{
  if( visited.find( n )==visited.end() ){
    Node ret = n;
    if( n.getKind()==FORALL ){
      QAttributes qa;
      QuantAttributes::computeQuantAttributes( n, qa );
      if( !qa.d_qid_num.isNull() ){
        //if it has an id, check whether we have done quantifier elimination for this id
        std::map< Node, Node >::iterator it = d_id_to_ce_quant.find( qa.d_qid_num );
        if( it!=d_id_to_ce_quant.end() ){
          Node ceq = it->second;
          bool doNestedQe = d_elim_quants.contains( ceq );
          if( doNestedQe ){
            ret = doNestedQENode( q, ceq, n, inst_terms, doVts );
          }else{
            Trace("cegqi-nqe") << "Add to nested qe waitlist : " << std::endl;
            Node nr = Rewriter::rewrite( n );
            Trace("cegqi-nqe") << "  " << ceq << std::endl;
            Trace("cegqi-nqe") << "  " << nr << std::endl;
            int wlsize = d_nested_qe_waitlist_size[ceq] + 1;
            d_nested_qe_waitlist_size[ceq] = wlsize;
            if( wlsize<(int)d_nested_qe_waitlist[ceq].size() ){
              d_nested_qe_waitlist[ceq][wlsize] = nr;
            }else{
              d_nested_qe_waitlist[ceq].push_back( nr );
            }
            d_nested_qe_info[nr].d_q = q;
            d_nested_qe_info[nr].d_inst_terms.clear();
            d_nested_qe_info[nr].d_inst_terms.insert( d_nested_qe_info[nr].d_inst_terms.end(), inst_terms.begin(), inst_terms.end() );
            d_nested_qe_info[nr].d_doVts = doVts;
            //TODO: ensure this holds by restricting prenex when cbqiNestedQe is true.
            Assert(!options::cegqiInnermost());
          }
        } 
      } 
    }else if( n.getNumChildren()>0 ){
      std::vector< Node > children;
      if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
        children.push_back( n.getOperator() );
      }
      bool childChanged = false;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        Node nc = doNestedQERec( q, n[i], visited, inst_terms, doVts );
        childChanged = childChanged || nc!=n[i];
        children.push_back( nc );
      }
      if( childChanged ){
        ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
      }
    }
    visited[n] = ret;
    return ret;
  }else{
    return n;
  }  
}

Node InstStrategyCegqi::doNestedQE(Node q,
                                   std::vector<Node>& inst_terms,
                                   Node lem,
                                   bool doVts)
{
  std::map< Node, Node > visited;
  return doNestedQERec( q, lem, visited, inst_terms, doVts );
}

void InstStrategyCegqi::registerCounterexampleLemma(Node q, Node lem)
{
  // must register with the instantiator
  // must explicitly remove ITEs so that we record dependencies
  std::vector<Node> ce_vars;
  TermUtil* tutil = d_quantEngine->getTermUtil();
  for (unsigned i = 0, nics = tutil->getNumInstantiationConstants(q); i < nics;
       i++)
  {
    ce_vars.push_back(tutil->getInstantiationConstant(q, i));
  }
  CegInstantiator* cinst = getInstantiator(q);
  LemmaStatus status = d_quantEngine->getOutputChannel().lemma(lem);
  Node ppLem = status.getRewrittenLemma();
  Trace("cegqi-debug") << "Counterexample lemma (post-preprocess): " << ppLem
                       << std::endl;
  std::vector<Node> auxLems;
  cinst->registerCounterexampleLemma(ppLem, ce_vars, auxLems);
  for (unsigned i = 0, size = auxLems.size(); i < size; i++)
  {
    Trace("cegqi-debug") << "Auxiliary CE lemma " << i << " : " << auxLems[i]
                         << std::endl;
    d_quantEngine->addLemma(auxLems[i], false);
  }
}

bool InstStrategyCegqi::doCbqi(Node q)
{
  std::map<Node, CegHandledStatus>::iterator it = d_do_cbqi.find(q);
  if( it==d_do_cbqi.end() ){
    CegHandledStatus ret = CegInstantiator::isCbqiQuant(q, d_quantEngine);
    Trace("cegqi-quant") << "doCbqi " << q << " returned " << ret << std::endl;
    d_do_cbqi[q] = ret;
    return ret != CEG_UNHANDLED;
  }
  return it->second != CEG_UNHANDLED;
}

void InstStrategyCegqi::process( Node q, Theory::Effort effort, int e ) {
  if( e==0 ){
    CegInstantiator * cinst = getInstantiator( q );
    Trace("inst-alg") << "-> Run cegqi for " << q << std::endl;
    d_curr_quant = q;
    if( !cinst->check() ){
      d_incomplete_check = true;
      d_check_vts_lemma_lc = true;
    }
    d_curr_quant = Node::null();
  }else if( e==1 ){
    //minimize the free delta heuristically on demand
    if( d_check_vts_lemma_lc ){
      Trace("inst-alg") << "-> Minimize delta heuristic, for " << q << std::endl;
      d_check_vts_lemma_lc = false;
      d_small_const = NodeManager::currentNM()->mkNode( MULT, d_small_const, d_small_const );
      d_small_const = Rewriter::rewrite( d_small_const );
      //heuristic for now, until we know how to do nested quantification
      Node delta = d_vtsCache->getVtsDelta(true, false);
      if( !delta.isNull() ){
        Trace("quant-vts-debug") << "Delta lemma for " << d_small_const << std::endl;
        Node delta_lem_ub = NodeManager::currentNM()->mkNode( LT, delta, d_small_const );
        d_quantEngine->getOutputChannel().lemma( delta_lem_ub );
      }
      std::vector< Node > inf;
      d_vtsCache->getVtsTerms(inf, true, false, false);
      for( unsigned i=0; i<inf.size(); i++ ){
        Trace("quant-vts-debug") << "Infinity lemma for " << inf[i] << " " << d_small_const << std::endl;
        Node inf_lem_lb = NodeManager::currentNM()->mkNode( GT, inf[i], NodeManager::currentNM()->mkConst( Rational(1)/d_small_const.getConst<Rational>() ) );
        d_quantEngine->getOutputChannel().lemma( inf_lem_lb );
      }
    }
  }
}

Node InstStrategyCegqi::getCounterexampleLiteral(Node q)
{
  std::map<Node, Node>::iterator it = d_ce_lit.find(q);
  if (it != d_ce_lit.end())
  {
    return it->second;
  }
  NodeManager * nm = NodeManager::currentNM();
  Node g = nm->mkSkolem("g", nm->booleanType());
  // ensure that it is a SAT literal
  Node ceLit = d_quantEngine->getValuation().ensureLiteral(g);
  d_ce_lit[q] = ceLit;
  return ceLit;
}

bool InstStrategyCegqi::doAddInstantiation( std::vector< Node >& subs ) {
  Assert(!d_curr_quant.isNull());
  //if doing partial quantifier elimination, record the instantiation and set the incomplete flag instead of sending instantiation lemma
  if( d_quantEngine->getQuantAttributes()->isQuantElimPartial( d_curr_quant ) ){
    d_cbqi_set_quant_inactive = true;
    d_incomplete_check = true;
    d_quantEngine->getInstantiate()->recordInstantiation(
        d_curr_quant, subs, false, false);
    return true;
  }else{
    //check if we need virtual term substitution (if used delta or infinity)
    bool used_vts = d_vtsCache->containsVtsTerm(subs, false);
    if (d_quantEngine->getInstantiate()->addInstantiation(
            d_curr_quant, subs, false, false, used_vts))
    {
      ++(d_quantEngine->d_statistics.d_instantiations_cbqi);
      //d_added_inst.insert( d_curr_quant );
      return true;
    }else{
      //this should never happen for monotonic selection strategies
      Trace("cegqi-warn") << "WARNING: Existing instantiation" << std::endl;
      return false;
    }
  }
}

bool InstStrategyCegqi::addLemma( Node lem ) {
  return d_quantEngine->addLemma( lem );
}


CegInstantiator * InstStrategyCegqi::getInstantiator( Node q ) {
  std::map<Node, std::unique_ptr<CegInstantiator>>::iterator it =
      d_cinst.find(q);
  if( it==d_cinst.end() ){
    d_cinst[q].reset(new CegInstantiator(q, this));
    return d_cinst[q].get();
  }
  return it->second.get();
}

VtsTermCache* InstStrategyCegqi::getVtsTermCache() const
{
  return d_vtsCache.get();
}

BvInverter* InstStrategyCegqi::getBvInverter() const
{
  return d_bv_invert.get();
}

void InstStrategyCegqi::presolve() {
  if (!options::cegqiPreRegInst())
  {
    return;
  }
  for (std::pair<const Node, std::unique_ptr<CegInstantiator>>& ci : d_cinst)
  {
    Trace("cegqi-presolve") << "Presolve " << ci.first << std::endl;
    ci.second->presolve(ci.first);
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
