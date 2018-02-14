/*********************                                                        */
/*! \file inst_strategy_cbqi.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of counterexample-guided quantifier instantiation strategies
 **/
#include "theory/quantifiers/cegqi/inst_strategy_cbqi.h"

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
#include "theory/quantifiers/ematching/trigger.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::theory::arith;

#define ARITH_INSTANTIATOR_USE_MINUS_DELTA

InstStrategyCbqi::InstStrategyCbqi( QuantifiersEngine * qe )
  : QuantifiersModule( qe ), d_added_cbqi_lemma( qe->getUserContext() ), 
d_elim_quants( qe->getSatContext() ),
d_nested_qe_waitlist_size( qe->getUserContext() ),
d_nested_qe_waitlist_proc( qe->getUserContext() )
//, d_added_inst( qe->getUserContext() )
{
  d_qid_count = 0;
}

bool InstStrategyCbqi::needsCheck( Theory::Effort e ) {
  return e>=Theory::EFFORT_LAST_CALL;
}

QuantifiersModule::QEffort InstStrategyCbqi::needsModel(Theory::Effort e)
{
  for( unsigned i=0; i<d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
    Node q = d_quantEngine->getModel()->getAssertedQuantifier( i );
    if( doCbqi( q ) && d_quantEngine->getModel()->isQuantifierActive( q ) ){
      return QEFFORT_STANDARD;
    }
  }
  return QEFFORT_NONE;
}

bool InstStrategyCbqi::registerCbqiLemma( Node q ) {
  if( !hasAddedCbqiLemma( q ) ){
    d_added_cbqi_lemma.insert( q );
    Trace("cbqi-debug") << "Do cbqi for " << q << std::endl;
    //add cbqi lemma
    //get the counterexample literal
    Node ceLit = d_quantEngine->getTermUtil()->getCounterexampleLiteral( q );
    Node ceBody = d_quantEngine->getTermUtil()->getInstConstantBody( q );
    if( !ceBody.isNull() ){
      //add counterexample lemma
      Node lem = NodeManager::currentNM()->mkNode( OR, ceLit.negate(), ceBody.negate() );
      //require any decision on cel to be phase=true
      d_quantEngine->addRequirePhase( ceLit, true );
      Debug("cbqi-debug") << "Require phase " << ceLit << " = true." << std::endl;
      //add counterexample lemma
      lem = Rewriter::rewrite( lem );
      Trace("cbqi-lemma") << "Counterexample lemma : " << lem << std::endl;
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
                Assert( !itc->second.empty() );
                Node ic = d_quantEngine->getTermUtil()->getInstantiationConstant( q, i );
                std::vector< Node > disj;
                for( unsigned j=0; j<itc->second.size(); j++ ){
                  disj.push_back( ic.eqNode( itc->second[j] ) );
                }
                Node tlem = disj.size()==1 ? disj[0] : NodeManager::currentNM()->mkNode( kind::OR, disj );
                Trace("cbqi-lemma") << "EPR totality lemma : " << tlem << std::endl;
                d_quantEngine->getOutputChannel().lemma( tlem );
              }else{
                Assert( false );
              }                  
            }else{
              Assert( !options::cbqiAll() );
            }
          }
        }
      }      
      
      //compute dependencies between quantified formulas
      if( options::cbqiLitDepend() || options::cbqiInnermost() ){
        std::vector< Node > ics;
        TermUtil::computeVarContains( q, ics );
        d_parent_quant[q].clear();
        d_children_quant[q].clear();
        std::vector< Node > dep;
        for( unsigned i=0; i<ics.size(); i++ ){
          Node qi = ics[i].getAttribute(InstConstantAttribute());
          if( std::find( d_parent_quant[q].begin(), d_parent_quant[q].end(), qi )==d_parent_quant[q].end() ){
            d_parent_quant[q].push_back( qi );
            d_children_quant[qi].push_back( q );
            Assert( hasAddedCbqiLemma( qi ) );
            Node qicel = d_quantEngine->getTermUtil()->getCounterexampleLiteral( qi );
            dep.push_back( qi );
            dep.push_back( qicel );
          }
        }
        if( !dep.empty() ){
          Node dep_lemma = NodeManager::currentNM()->mkNode( kind::IMPLIES, ceLit, NodeManager::currentNM()->mkNode( kind::AND, dep ) );
          Trace("cbqi-lemma") << "Counterexample dependency lemma : " << dep_lemma << std::endl;
          d_quantEngine->getOutputChannel().lemma( dep_lemma );
        }
      }
      
      //must register all sub-quantifiers of counterexample lemma, register their lemmas
      std::vector< Node > quants;
      TermUtil::computeQuantContains( lem, quants );
      for( unsigned i=0; i<quants.size(); i++ ){
        if( doCbqi( quants[i] ) ){
          registerCbqiLemma( quants[i] );
        }
        if( options::cbqiNestedQE() ){
          //record these as counterexample quantifiers
          QAttributes qa;
          QuantAttributes::computeQuantAttributes( quants[i], qa );
          if( !qa.d_qid_num.isNull() ){
            d_id_to_ce_quant[ qa.d_qid_num ] = quants[i];
            d_ce_quant_to_id[ quants[i] ] = qa.d_qid_num;
            Trace("cbqi-nqe") << "CE quant id = " << qa.d_qid_num << " is " << quants[i] << std::endl;
          }
        }
      }
    }
    return true;
  }else{
    return false;
  }
}

void InstStrategyCbqi::reset_round( Theory::Effort effort ) {
  d_cbqi_set_quant_inactive = false;
  d_incomplete_check = false;
  d_active_quant.clear();
  //check if any cbqi lemma has not been added yet
  for( unsigned i=0; i<d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
    Node q = d_quantEngine->getModel()->getAssertedQuantifier( i );
    //it is not active if it corresponds to a rewrite rule: we will process in rewrite engine
    if( doCbqi( q ) ){
      Assert( hasAddedCbqiLemma( q ) );
      if( d_quantEngine->getModel()->isQuantifierActive( q ) ){
        d_active_quant[q] = true;
        Debug("cbqi-debug") << "Check quantified formula " << q << "..." << std::endl;
        Node cel = d_quantEngine->getTermUtil()->getCounterexampleLiteral( q );
        bool value;
        if( d_quantEngine->getValuation().hasSatValue( cel, value ) ){
          Debug("cbqi-debug") << "...CE Literal has value " << value << std::endl;
          if( !value ){
            if( d_quantEngine->getValuation().isDecision( cel ) ){
              Trace("cbqi-warn") << "CBQI WARNING: Bad decision on CE Literal." << std::endl;
            }else{
              Trace("cbqi") << "Inactive : " << q << std::endl;
              d_quantEngine->getModel()->setQuantifierActive( q, false );
              d_cbqi_set_quant_inactive = true;
              d_active_quant.erase( q );
              d_elim_quants.insert( q );
              Trace("cbqi-nqe") << "Inactive, waitlist proc/size = " << d_nested_qe_waitlist_proc[q].get() << "/" << d_nested_qe_waitlist_size[q].get() << std::endl;
              //process from waitlist
              while( d_nested_qe_waitlist_proc[q]<d_nested_qe_waitlist_size[q] ){
                int index = d_nested_qe_waitlist_proc[q];
                Assert( index>=0 );
                Assert( index<(int)d_nested_qe_waitlist[q].size() );
                Node nq = d_nested_qe_waitlist[q][index];
                Node nqeqn = doNestedQENode( d_nested_qe_info[nq].d_q, q, nq, d_nested_qe_info[nq].d_inst_terms, d_nested_qe_info[nq].d_doVts );
                Node dqelem = nq.eqNode( nqeqn ); 
                Trace("cbqi-lemma") << "Delayed nested quantifier elimination lemma : " << dqelem << std::endl;
                d_quantEngine->getOutputChannel().lemma( dqelem );
                d_nested_qe_waitlist_proc[q] = index + 1;
              }
            }
          }
        }else{
          Debug("cbqi-debug") << "...CE Literal does not have value " << std::endl;
        }
      }
    }
  }

  //refinement: only consider innermost active quantified formulas
  if( options::cbqiInnermost() ){
    if( !d_children_quant.empty() && !d_active_quant.empty() ){
      Trace("cbqi-debug") << "Find non-innermost quantifiers..." << std::endl;
      std::vector< Node > ninner;
      for( std::map< Node, bool >::iterator it = d_active_quant.begin(); it != d_active_quant.end(); ++it ){
        std::map< Node, std::vector< Node > >::iterator itc = d_children_quant.find( it->first );
        if( itc!=d_children_quant.end() ){
          for( unsigned j=0; j<itc->second.size(); j++ ){
            if( d_active_quant.find( itc->second[j] )!=d_active_quant.end() ){
              Trace("cbqi-debug") << "Do not consider " << it->first << " since it is not innermost (" << itc->second[j] << std::endl;
              ninner.push_back( it->first );
              break;
            }
          }
        }
      } 
      Trace("cbqi-debug") << "Found " << ninner.size() << " non-innermost." << std::endl;
      for( unsigned i=0; i<ninner.size(); i++ ){
        Assert( d_active_quant.find( ninner[i] )!=d_active_quant.end() );
        d_active_quant.erase( ninner[i] );
      }
      Assert( !d_active_quant.empty() );
      Trace("cbqi-debug") << "...done removing." << std::endl;
    }
  }
  
  processResetInstantiationRound( effort );
}

void InstStrategyCbqi::check(Theory::Effort e, QEffort quant_e)
{
  if (quant_e == QEFFORT_STANDARD)
  {
    Assert( !d_quantEngine->inConflict() );
    double clSet = 0;
    if( Trace.isOn("cbqi-engine") ){
      clSet = double(clock())/double(CLOCKS_PER_SEC);
      Trace("cbqi-engine") << "---Cbqi Engine Round, effort = " << e << "---" << std::endl;
    }
    unsigned lastWaiting = d_quantEngine->getNumLemmasWaiting();
    for( int ee=0; ee<=1; ee++ ){
      //for( unsigned i=0; i<d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
      //  Node q = d_quantEngine->getModel()->getAssertedQuantifier( i );
      //  if( doCbqi( q ) && d_quantEngine->getModel()->isQuantifierActive( q ) ){
      for( std::map< Node, bool >::iterator it = d_active_quant.begin(); it != d_active_quant.end(); ++it ){
        Node q = it->first;
        Trace("cbqi") << "CBQI : Process quantifier " << q[0] << " at effort " << ee << std::endl;
        if( d_nested_qe.find( q )==d_nested_qe.end() ){
          process( q, e, ee );
          if( d_quantEngine->inConflict() ){
            break;
          }
        }else{
          Trace("cbqi-warn") << "CBQI : Cannot process already eliminated quantified formula " << q << std::endl;
          Assert( false );
        }
      }
      if( d_quantEngine->inConflict() || d_quantEngine->getNumLemmasWaiting()>lastWaiting ){
        break;
      }
    }
    if( Trace.isOn("cbqi-engine") ){
      if( d_quantEngine->getNumLemmasWaiting()>lastWaiting ){
        Trace("cbqi-engine") << "Added lemmas = " << (d_quantEngine->getNumLemmasWaiting()-lastWaiting) << std::endl;
      }
      double clSet2 = double(clock())/double(CLOCKS_PER_SEC);
      Trace("cbqi-engine") << "Finished cbqi engine, time = " << (clSet2-clSet) << std::endl;
    }
  }
}

bool InstStrategyCbqi::checkComplete() {
  if( ( !options::cbqiSat() && d_cbqi_set_quant_inactive ) || d_incomplete_check ){
    return false;
  }else{
    return true;
  }
}

bool InstStrategyCbqi::checkCompleteFor( Node q ) {
  std::map< Node, int >::iterator it = d_do_cbqi.find( q );
  if( it!=d_do_cbqi.end() ){
    return it->second>0;
  }else{
    return false;
  }
}

Node InstStrategyCbqi::getIdMarkedQuantNode( Node n, std::map< Node, Node >& visited ){
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

void InstStrategyCbqi::preRegisterQuantifier( Node q ) {
  if( d_quantEngine->getOwner( q )==NULL && doCbqi( q ) ){
    if( d_do_cbqi[q]==2 ){
      //take full ownership of the quantified formula
      d_quantEngine->setOwner( q, this );
      
      //mark all nested quantifiers with id
      if( options::cbqiNestedQE() ){
        std::map< Node, Node > visited;
        Node mq = getIdMarkedQuantNode( q[1], visited );
        if( mq!=q[1] ){
          //do not do cbqi
          d_do_cbqi[q] = false;
          //instead do reduction
          std::vector< Node > qqc;
          qqc.push_back( q[0] );
          qqc.push_back( mq );
          if( q.getNumChildren()==3 ){
            qqc.push_back( q[2] );
          }
          Node qq = NodeManager::currentNM()->mkNode( FORALL, qqc );
          Node mlem = NodeManager::currentNM()->mkNode( IMPLIES, q, qq );
          Trace("cbqi-lemma") << "Mark quant id lemma : " << mlem << std::endl;
          d_quantEngine->getOutputChannel().lemma( mlem );
        }
      }
    }
  }
}

void InstStrategyCbqi::registerQuantifier( Node q ) {
  if( doCbqi( q ) ){
    if( registerCbqiLemma( q ) ){
      Trace("cbqi") << "Registered cbqi lemma for quantifier : " << q << std::endl;
    }
  }
}

Node InstStrategyCbqi::doNestedQENode( Node q, Node ceq, Node n, std::vector< Node >& inst_terms, bool doVts ) {
  // there is a nested quantified formula (forall y. nq[y,x]) such that 
  //    q is (forall y. nq[y,t]) for ground terms t,
  //    ceq is (forall y. nq[y,e]) for CE variables e.
  // we call this function when we know (forall y. nq[y,e]) is equivalent to quantifier-free formula C[e].
  // in this case, q is equivalent to the quantifier-free formula C[t].
  if( d_nested_qe.find( ceq )==d_nested_qe.end() ){
    d_nested_qe[ceq] = d_quantEngine->getInstantiatedConjunction( ceq );
    Trace("cbqi-nqe") << "CE quantifier elimination : " << std::endl;
    Trace("cbqi-nqe") << "  " << ceq << std::endl; 
    Trace("cbqi-nqe") << "  " << d_nested_qe[ceq] << std::endl;
    //should not contain quantifiers
    Assert( !QuantifiersRewriter::containsQuantifiers( d_nested_qe[ceq] ) );
  }
  Assert( d_quantEngine->getTermUtil()->d_inst_constants[q].size()==inst_terms.size() );
  //replace inst constants with instantiation
  Node ret = d_nested_qe[ceq].substitute( d_quantEngine->getTermUtil()->d_inst_constants[q].begin(),
                                          d_quantEngine->getTermUtil()->d_inst_constants[q].end(),
                                          inst_terms.begin(), inst_terms.end() );
  if( doVts ){
    //do virtual term substitution
    ret = Rewriter::rewrite( ret );
    ret = d_quantEngine->getTermUtil()->rewriteVtsSymbols( ret );
  }
  Trace("cbqi-nqe") << "Nested quantifier elimination: " << std::endl;
  Trace("cbqi-nqe") << "  " << n << std::endl; 
  Trace("cbqi-nqe") << "  " << ret << std::endl;
  return ret;
}

Node InstStrategyCbqi::doNestedQERec( Node q, Node n, std::map< Node, Node >& visited, std::vector< Node >& inst_terms, bool doVts ) {
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
            Trace("cbqi-nqe") << "Add to nested qe waitlist : " << std::endl;
            Node nr = Rewriter::rewrite( n );
            Trace("cbqi-nqe") << "  " << ceq << std::endl;
            Trace("cbqi-nqe") << "  " << nr << std::endl;
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
            Assert( !options::cbqiInnermost() );
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

Node InstStrategyCbqi::doNestedQE( Node q, std::vector< Node >& inst_terms, Node lem, bool doVts ) {
  std::map< Node, Node > visited;
  return doNestedQERec( q, lem, visited, inst_terms, doVts );
}

void InstStrategyCbqi::registerCounterexampleLemma( Node q, Node lem ){
  Trace("cbqi-debug") << "Counterexample lemma  : " << lem << std::endl;
  d_quantEngine->addLemma( lem, false );
}

bool InstStrategyCbqi::hasNonCbqiOperator( Node n, std::map< Node, bool >& visited ){
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    if( n.getKind()!=BOUND_VARIABLE && TermUtil::hasBoundVarAttr( n ) ){
      if( !inst::Trigger::isCbqiKind( n.getKind() ) ){
        Trace("cbqi-debug2") << "Non-cbqi kind : " << n.getKind() << " in " << n  << std::endl;
        return true;
      }else if( n.getKind()==MULT && ( n.getNumChildren()!=2 || !n[0].isConst() ) ){
        Trace("cbqi-debug2") << "Non-linear arithmetic : " << n << std::endl;
        return true;
      }else if( n.getKind()==FORALL ){
        return hasNonCbqiOperator( n[1], visited );
      }else{
        for( unsigned i=0; i<n.getNumChildren(); i++ ){
          if( hasNonCbqiOperator( n[i], visited ) ){
            return true;
          }
        }
      }
    }
  }
  return false;
}

// -1 : not cbqi sort, 0 : cbqi sort, 1 : cbqi sort regardless of quantifier body
int InstStrategyCbqi::isCbqiSort( TypeNode tn, std::map< TypeNode, int >& visited ) {
  std::map< TypeNode, int >::iterator itv = visited.find( tn );
  if( itv==visited.end() ){
    visited[tn] = 0;
    int ret = -1;
    if( tn.isInteger() || tn.isReal() || tn.isBoolean() || tn.isBitVector() ){
      ret = 0;
    }else if( tn.isDatatype() ){
      ret = 1;
      const Datatype& dt = ((DatatypeType)tn.toType()).getDatatype();
      for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
        for( unsigned j=0; j<dt[i].getNumArgs(); j++ ){
          TypeNode crange = TypeNode::fromType( ((SelectorType)dt[i][j].getType()).getRangeType() );
          int cret = isCbqiSort( crange, visited );
          if( cret==-1 ){
            visited[tn] = -1;
            return -1;
          }else if( cret<ret ){
            ret = cret;
          }
        }
      }
    }else if( tn.isSort() ){
      QuantEPR * qepr = d_quantEngine->getQuantEPR();
      if( qepr!=NULL ){
        ret = qepr->isEPR( tn ) ? 1 : -1;
      }
    }
    visited[tn] = ret;
    return ret;
  }else{
    return itv->second;
  }
}

int InstStrategyCbqi::hasNonCbqiVariable( Node q ){
  int hmin = 1;
  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
    TypeNode tn = q[0][i].getType();
    std::map< TypeNode, int > visited;
    int handled = isCbqiSort( tn, visited );
    if( handled==-1 ){
      return -1;
    }else if( handled<hmin ){
      hmin = handled;
    }
  }
  return hmin;
}

bool InstStrategyCbqi::doCbqi( Node q ){
  std::map< Node, int >::iterator it = d_do_cbqi.find( q );
  if( it==d_do_cbqi.end() ){
    int ret = 2;
    if( !d_quantEngine->getQuantAttributes()->isQuantElim( q ) ){
      Assert( !d_quantEngine->getQuantAttributes()->isQuantElimPartial( q ) );
      //if has an instantiation pattern, don't do it
      if( q.getNumChildren()==3 && options::eMatching() && options::userPatternsQuant()!=USER_PAT_MODE_IGNORE ){
        for( unsigned i=0; i<q[2].getNumChildren(); i++ ){
          if( q[2][i].getKind()==INST_PATTERN ){
            ret = 0;
          }
        }
      }
      if( d_quantEngine->getQuantAttributes()->isSygus( q ) ){
        ret = 0;
      }
      if( ret!=0 ){
        //if quantifier has a non-handled variable, then do not use cbqi
        //if quantifier has an APPLY_UF term, then do not use cbqi unless EPR
        int ncbqiv = hasNonCbqiVariable( q );
        if( ncbqiv==0 || ncbqiv==1 ){
          std::map< Node, bool > visited;
          if( hasNonCbqiOperator( q[1], visited ) ){
            if( ncbqiv==1 ){
              //all variables are fully handled, this implies this will be handlable regardless of body (e.g. for EPR)
              //  so, try but not exclusively
              ret = 1;
            }else{
              //cannot be handled
              ret = 0;
            }
          }
        }else{
          // unhandled variable type
          ret = 0;
        }
        if( ret==0 && options::cbqiAll() ){
          //try but not exclusively
          ret = 1;
        }
      }
    }
    Trace("cbqi-quant") << "doCbqi " << q << " returned " << ret << std::endl;
    d_do_cbqi[q] = ret;
    return ret!=0;
  }else{
    return it->second!=0;
  }
}

Node InstStrategyCbqi::getNextDecisionRequestProc( Node q, std::map< Node, bool >& proc ) {
  if( proc.find( q )==proc.end() ){
    proc[q] = true;
    //first check children
    std::map< Node, std::vector< Node > >::iterator itc = d_children_quant.find( q );
    if( itc!=d_children_quant.end() ){
      for( unsigned j=0; j<itc->second.size(); j++ ){
        Node d = getNextDecisionRequestProc( itc->second[j], proc );
        if( !d.isNull() ){
          return d;
        }
      }
    }
    //then check self
    if( hasAddedCbqiLemma( q ) ){
      Node cel = d_quantEngine->getTermUtil()->getCounterexampleLiteral( q );
      bool value;
      if( !d_quantEngine->getValuation().hasSatValue( cel, value ) ){
        Trace("cbqi-dec") << "CBQI: get next decision " << cel << std::endl;
        return cel;
      }
    }    
  }
  return Node::null(); 
}

Node InstStrategyCbqi::getNextDecisionRequest( unsigned& priority ){
  std::map< Node, bool > proc;
  //for( unsigned i=0; i<d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
  //  Node q = d_quantEngine->getModel()->getAssertedQuantifier( i );
  for( NodeSet::const_iterator it = d_added_cbqi_lemma.begin(); it != d_added_cbqi_lemma.end(); ++it ){
    Node q = *it;
    Node d = getNextDecisionRequestProc( q, proc );
    if( !d.isNull() ){
      priority = 0;
      return d;
    }
  }
  return Node::null();
}



//new implementation

bool CegqiOutputInstStrategy::doAddInstantiation( std::vector< Node >& subs ) {
  return d_out->doAddInstantiation( subs );
}

bool CegqiOutputInstStrategy::isEligibleForInstantiation( Node n ) {
  return d_out->isEligibleForInstantiation( n );
}

bool CegqiOutputInstStrategy::addLemma( Node lem ) {
  return d_out->addLemma( lem );
}


InstStrategyCegqi::InstStrategyCegqi( QuantifiersEngine * qe )
  : InstStrategyCbqi( qe ) {
  d_out = new CegqiOutputInstStrategy( this );
  d_small_const = NodeManager::currentNM()->mkConst( Rational(1)/Rational(1000000) );
  d_check_vts_lemma_lc = false;
}

InstStrategyCegqi::~InstStrategyCegqi()
{
  delete d_out;

  for(std::map< Node, CegInstantiator * >::iterator i = d_cinst.begin(),
          iend = d_cinst.end(); i != iend; ++i) {
    CegInstantiator * instantiator = (*i).second;
    delete instantiator;
  }
  d_cinst.clear();
}

void InstStrategyCegqi::processResetInstantiationRound( Theory::Effort effort ) {
  d_check_vts_lemma_lc = false;
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
      Node delta = d_quantEngine->getTermUtil()->getVtsDelta( true, false );
      if( !delta.isNull() ){
        Trace("quant-vts-debug") << "Delta lemma for " << d_small_const << std::endl;
        Node delta_lem_ub = NodeManager::currentNM()->mkNode( LT, delta, d_small_const );
        d_quantEngine->getOutputChannel().lemma( delta_lem_ub );
      }
      std::vector< Node > inf;
      d_quantEngine->getTermUtil()->getVtsTerms( inf, true, false, false );
      for( unsigned i=0; i<inf.size(); i++ ){
        Trace("quant-vts-debug") << "Infinity lemma for " << inf[i] << " " << d_small_const << std::endl;
        Node inf_lem_lb = NodeManager::currentNM()->mkNode( GT, inf[i], NodeManager::currentNM()->mkConst( Rational(1)/d_small_const.getConst<Rational>() ) );
        d_quantEngine->getOutputChannel().lemma( inf_lem_lb );
      }
    }
  }
}

bool InstStrategyCegqi::doAddInstantiation( std::vector< Node >& subs ) {
  Assert( !d_curr_quant.isNull() );
  //if doing partial quantifier elimination, record the instantiation and set the incomplete flag instead of sending instantiation lemma
  if( d_quantEngine->getQuantAttributes()->isQuantElimPartial( d_curr_quant ) ){
    d_cbqi_set_quant_inactive = true;
    d_incomplete_check = true;
    d_quantEngine->getInstantiate()->recordInstantiation(
        d_curr_quant, subs, false, false);
    return true;
  }else{
    //check if we need virtual term substitution (if used delta or infinity)
    bool used_vts = d_quantEngine->getTermUtil()->containsVtsTerm( subs, false );
    if (d_quantEngine->getInstantiate()->addInstantiation(
            d_curr_quant, subs, false, false, used_vts))
    {
      ++(d_quantEngine->d_statistics.d_instantiations_cbqi);
      //d_added_inst.insert( d_curr_quant );
      return true;
    }else{
      //this should never happen for monotonic selection strategies
      Trace("cbqi-warn") << "WARNING: Existing instantiation" << std::endl;
      return false;
    }
  }
}

bool InstStrategyCegqi::addLemma( Node lem ) {
  return d_quantEngine->addLemma( lem );
}

bool InstStrategyCegqi::isEligibleForInstantiation( Node n ) {
  if( n.getKind()==INST_CONSTANT || n.getKind()==SKOLEM ){
    if( n.getAttribute(VirtualTermSkolemAttribute()) ){
      // virtual terms are allowed
      return true;
    }else{
      TypeNode tn = n.getType();
      if( tn.isSort() ){
        QuantEPR * qepr = d_quantEngine->getQuantEPR();
        if( qepr!=NULL ){
          //legal if in the finite set of constants of type tn
          if( qepr->isEPRConstant( tn, n ) ){
            return true;
          }
        }
      }
      //only legal if current quantified formula contains n
      return TermUtil::containsTerm( d_curr_quant, n );
    }
  }else{
    return true;
  }
}

CegInstantiator * InstStrategyCegqi::getInstantiator( Node q ) {
  std::map< Node, CegInstantiator * >::iterator it = d_cinst.find( q );
  if( it==d_cinst.end() ){
    CegInstantiator * cinst = new CegInstantiator( d_quantEngine, d_out, true, true );
    d_cinst[q] = cinst;
    return cinst;
  }else{
   return it->second;
  }
}

void InstStrategyCegqi::registerQuantifier( Node q ) {
  if( doCbqi( q ) ){
    // get the instantiator  
    if( options::cbqiPreRegInst() ){
      getInstantiator( q );
    }
    // register the cbqi lemma
    if( registerCbqiLemma( q ) ){
      Trace("cbqi") << "Registered cbqi lemma for quantifier : " << q << std::endl;
    }
  }
}

void InstStrategyCegqi::registerCounterexampleLemma( Node q, Node lem ) {
  //must register with the instantiator
  //must explicitly remove ITEs so that we record dependencies
  std::vector< Node > ce_vars;
  for( unsigned i=0; i<d_quantEngine->getTermUtil()->getNumInstantiationConstants( q ); i++ ){
    ce_vars.push_back( d_quantEngine->getTermUtil()->getInstantiationConstant( q, i ) );
  }
  std::vector< Node > lems;
  lems.push_back( lem );
  CegInstantiator * cinst = getInstantiator( q );
  cinst->registerCounterexampleLemma( lems, ce_vars );
  for( unsigned i=0; i<lems.size(); i++ ){
    Trace("cbqi-debug") << "Counterexample lemma " << i << " : " << lems[i] << std::endl;
    d_quantEngine->addLemma( lems[i], false );
  }
}

void InstStrategyCegqi::presolve() {
  if( options::cbqiPreRegInst() ){
    for( std::map< Node, CegInstantiator * >::iterator it = d_cinst.begin(); it != d_cinst.end(); ++it ){
      Trace("cbqi-presolve") << "Presolve " << it->first << std::endl;
      it->second->presolve( it->first );
    }
  }
}

