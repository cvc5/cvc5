/*********************                                                        */
/*! \file ce_guided_instantiation.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief counterexample guided instantiation class
 **
 **/

#include "theory/quantifiers/ce_guided_instantiation.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers/options.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/first_order_model.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace std;

namespace CVC4 {

CegInstantiation::CegConjecture::CegConjecture( context::Context* c ) : d_active( c, false ), d_infeasible( c, false ), d_curr_lit( c, 0 ){

}

void CegInstantiation::CegConjecture::assign( Node q ) {
  Assert( d_quant.isNull() );
  Assert( q.getKind()==FORALL );
  d_quant = q;
  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
    d_candidates.push_back( NodeManager::currentNM()->mkSkolem( "e", q[0][i].getType() ) );
  }
}

void CegInstantiation::CegConjecture::initializeGuard( QuantifiersEngine * qe ){
  if( d_guard.isNull() ){
    d_guard = Rewriter::rewrite( NodeManager::currentNM()->mkSkolem( "G", NodeManager::currentNM()->booleanType() ) );
    //specify guard behavior
    d_guard = qe->getValuation().ensureLiteral( d_guard );
    AlwaysAssert( !d_guard.isNull() );
    qe->getOutputChannel().requirePhase( d_guard, true );
  }
}

Node CegInstantiation::CegConjecture::getLiteral( QuantifiersEngine * qe, int i ) {
  if( d_measure_term.isNull() ){
    return Node::null();
  }else{
    std::map< int, Node >::iterator it = d_lits.find( i );
    if( it==d_lits.end() ){
      Node lit = NodeManager::currentNM()->mkNode( LEQ, d_measure_term, NodeManager::currentNM()->mkConst( Rational( i ) ) );
      lit = Rewriter::rewrite( lit );
      d_lits[i] = lit;

      Node lem = NodeManager::currentNM()->mkNode( kind::OR, lit, lit.negate() );
      Trace("cegqi-lemma") << "Fairness split : " << lem << std::endl;
      qe->getOutputChannel().lemma( lem );
      qe->getOutputChannel().requirePhase( lit, true );
      return lit;
    }else{
      return it->second;
    }
  }
}

CegInstantiation::CegInstantiation( QuantifiersEngine * qe, context::Context* c ) : QuantifiersModule( qe ){
  d_conj = new CegConjecture( d_quantEngine->getSatContext() );
}

bool CegInstantiation::needsCheck( Theory::Effort e ) {
  return e>=Theory::EFFORT_LAST_CALL;
}

bool CegInstantiation::needsModel( Theory::Effort e ) {
  return true;
}

void CegInstantiation::check( Theory::Effort e, unsigned quant_e ) {
  if( quant_e==QuantifiersEngine::QEFFORT_MODEL ){
    Trace("cegqi-engine") << "---Countexample Guided Instantiation Engine---" << std::endl;
    Trace("cegqi-engine-debug") << std::endl;
    Trace("cegqi-engine-debug") << "Current conjecture status : active : " << d_conj->d_active << " feasible : " << !d_conj->d_infeasible << std::endl;
    if( d_conj->d_active && !d_conj->d_infeasible ){
      checkCegConjecture( d_conj );
    }
    Trace("cegqi-engine") << "Finished Countexample Guided Instantiation engine." << std::endl;
  }
}

void CegInstantiation::registerQuantifier( Node q ) {
  if( d_quantEngine->getOwner( q )==this ){
    if( !d_conj->isAssigned() ){
      Trace("cegqi") << "Register conjecture : " << q << std::endl;
      d_conj->assign( q );
      //construct base instantiation
      d_conj->d_base_inst = Rewriter::rewrite( d_quantEngine->getInstantiation( q, d_conj->d_candidates ) );
      Trace("cegqi") << "Base instantiation is : " << d_conj->d_base_inst << std::endl;
      if( getTermDatabase()->isQAttrSygus( q ) ){
        Assert( d_conj->d_base_inst.getKind()==NOT );
        Assert( d_conj->d_base_inst[0].getKind()==FORALL );
        for( unsigned j=0; j<d_conj->d_base_inst[0][0].getNumChildren(); j++ ){
          d_conj->d_inner_vars.push_back( d_conj->d_base_inst[0][0][j] );
        }
      }else if( getTermDatabase()->isQAttrSynthesis( q ) ){
        //add immediate lemma
        Node lem = NodeManager::currentNM()->mkNode( OR, d_conj->d_guard.negate(), d_conj->d_base_inst );
        d_quantEngine->getOutputChannel().lemma( lem );
      }
      //fairness
      if( options::ceGuidedInstFair()!=CEGQI_FAIR_NONE ){
        std::vector< Node > mc;
        for( unsigned j=0; j<d_conj->d_candidates.size(); j++ ){
          TypeNode tn = d_conj->d_candidates[j].getType();
          if( options::ceGuidedInstFair()==CEGQI_FAIR_DT_SIZE ){
            if( tn.isDatatype() ){
              mc.push_back( NodeManager::currentNM()->mkNode( DT_SIZE, d_conj->d_candidates[j] ) );
            }
          }else if( options::ceGuidedInstFair()==CEGQI_FAIR_UF_DT_SIZE ){
            registerMeasuredType( tn );
            std::map< TypeNode, Node >::iterator it = d_uf_measure.find( tn );
            if( it!=d_uf_measure.end() ){
              mc.push_back( NodeManager::currentNM()->mkNode( APPLY_UF, it->second, d_conj->d_candidates[j] ) );
            }
          }
        }
        if( !mc.empty() ){
          d_conj->d_measure_term = mc.size()==1 ? mc[0] : NodeManager::currentNM()->mkNode( PLUS, mc );
          Trace("cegqi") << "Measure term is : " << d_conj->d_measure_term << std::endl;
        }
      }
    }else{
      Assert( d_conj->d_quant==q );
    }
  }
}

void CegInstantiation::assertNode( Node n ) {
  Trace("cegqi-debug") << "Cegqi : Assert : " << n << std::endl;
  bool pol = n.getKind()!=NOT;
  Node lit = n.getKind()==NOT ? n[0] : n;
  if( lit==d_conj->d_guard ){
    //d_guard_assertions[lit] = pol;
    d_conj->d_infeasible = !pol;
  }
  if( lit==d_conj->d_quant ){
    d_conj->d_active = true;
  }
}

Node CegInstantiation::getNextDecisionRequest() {
  d_conj->initializeGuard( d_quantEngine );
  bool value;
  if( !d_quantEngine->getValuation().hasSatValue( d_conj->d_guard, value ) ) {
    if( d_conj->d_guard_split.isNull() ){
      Node lem = NodeManager::currentNM()->mkNode( OR, d_conj->d_guard.negate(), d_conj->d_guard );
      d_quantEngine->getOutputChannel().lemma( lem );
    }
    Trace("cegqi-debug") << "CEGQI : Decide next on : " << d_conj->d_guard << "..." << std::endl;
    return d_conj->d_guard;
  }
  //enforce fairness
  if( d_conj->isAssigned() && options::ceGuidedInstFair()!=CEGQI_FAIR_NONE ){
    Node lit = d_conj->getLiteral( d_quantEngine, d_conj->d_curr_lit.get() );
    if( d_quantEngine->getValuation().hasSatValue( lit, value ) ) {
      if( !value ){
        d_conj->d_curr_lit.set( d_conj->d_curr_lit.get() + 1 );
        lit = d_conj->getLiteral( d_quantEngine, d_conj->d_curr_lit.get() );
        Trace("cegqi-debug") << "CEGQI : Decide on next lit : " << lit << "..." << std::endl;
        return lit;
      }
    }else{
      Trace("cegqi-debug") << "CEGQI : Decide on current lit : " << lit << "..." << std::endl;
      return lit;
    }
  }

  return Node::null();
}

void CegInstantiation::checkCegConjecture( CegConjecture * conj ) {
  Node q = conj->d_quant;
  Trace("cegqi-engine") << "Synthesis conjecture : " << q << std::endl;
  Trace("cegqi-engine") << "  * Candidate program/output symbol : ";
  for( unsigned i=0; i<conj->d_candidates.size(); i++ ){
    Trace("cegqi-engine") << conj->d_candidates[i] << " ";
  }
  Trace("cegqi-engine") << std::endl;
  if( options::ceGuidedInstFair()!=CEGQI_FAIR_NONE ){
    Trace("cegqi-engine") << "  * Current term size : " << conj->d_curr_lit.get() << std::endl;
  }

  if( conj->d_ce_sk.empty() ){
    Trace("cegqi-engine") << "  *** Check candidate phase..." << std::endl;
    if( getTermDatabase()->isQAttrSygus( q ) ){

      std::vector< Node > model_values;
      if( getModelValues( conj->d_candidates, model_values ) ){
        //check if we must apply fairness lemmas
        std::vector< Node > lems;
        if( options::ceGuidedInstFair()==CEGQI_FAIR_UF_DT_SIZE ){
          for( unsigned j=0; j<conj->d_candidates.size(); j++ ){
            getMeasureLemmas( conj->d_candidates[j], model_values[j], lems );
          }
        }
        if( !lems.empty() ){
          for( unsigned j=0; j<lems.size(); j++ ){
            Trace("cegqi-lemma") << "Measure lemma : " << lems[j] << std::endl;
            d_quantEngine->addLemma( lems[j] );
          }
          Trace("cegqi-engine") << "  ...refine size." << std::endl;
        }else{
          //must get a counterexample to the value of the current candidate
          Node inst = conj->d_base_inst.substitute( conj->d_candidates.begin(), conj->d_candidates.end(), model_values.begin(), model_values.end() );
          inst = Rewriter::rewrite( inst );
          //body should be an existential
          Assert( inst.getKind()==NOT );
          Assert( inst[0].getKind()==FORALL );
          //immediately skolemize
          Node inst_sk = getTermDatabase()->getSkolemizedBody( inst[0] );
          Trace("cegqi-lemma") << "Counterexample lemma : " << inst_sk << std::endl;
          d_quantEngine->addLemma( NodeManager::currentNM()->mkNode( OR, q.negate(), inst_sk.negate() ) );
          conj->d_ce_sk.push_back( inst[0] );
          Trace("cegqi-engine") << "  ...find counterexample." << std::endl;
        }
      }

    }else if( getTermDatabase()->isQAttrSynthesis( q ) ){
      std::vector< Node > model_terms;
      for( unsigned i=0; i<conj->d_candidates.size(); i++ ){
        Node t = getModelTerm( conj->d_candidates[i] );
        model_terms.push_back( t );
      }
      d_quantEngine->addInstantiation( q, model_terms, false );
    }
  }else{
    Trace("cegqi-engine") << "  *** Refine candidate phase..." << std::endl;
    for( unsigned j=0; j<conj->d_ce_sk.size(); j++ ){
      Node ce_q = conj->d_ce_sk[j];
      Assert( conj->d_inner_vars.size()==getTermDatabase()->d_skolem_constants[ce_q].size() );
      std::vector< Node > model_values;
      if( getModelValues( getTermDatabase()->d_skolem_constants[ce_q], model_values ) ){
        //candidate refinement : the next candidate must satisfy the counterexample found for the current model of the candidate
        Node inst_ce_refine = conj->d_base_inst[0][1].substitute( conj->d_inner_vars.begin(), conj->d_inner_vars.end(),
                                                                  model_values.begin(), model_values.end() );
        Node lem = NodeManager::currentNM()->mkNode( OR, conj->d_guard.negate(), inst_ce_refine );
        Trace("cegqi-lemma") << "Candidate refinement lemma : " << lem << std::endl;
        Trace("cegqi-engine") << "  ...refine candidate." << std::endl;
        d_quantEngine->addLemma( lem );
      }
    }
    conj->d_ce_sk.clear();
  }
}

bool CegInstantiation::getModelValues( std::vector< Node >& n, std::vector< Node >& v ) {
  bool success = true;
  Trace("cegqi-engine") << "  * Value is : ";
  for( unsigned i=0; i<n.size(); i++ ){
    Node nv = getModelValue( n[i] );
    v.push_back( nv );
    Trace("cegqi-engine") << nv << " ";
    if( nv.isNull() ){
      success = false;
    }
  }
  Trace("cegqi-engine") << std::endl;
  return success;
}

Node CegInstantiation::getModelValue( Node n ) {
  Trace("cegqi-mv") << "getModelValue for : " << n << std::endl;
  return d_quantEngine->getModel()->getValue( n );
}

Node CegInstantiation::getModelTerm( Node n ){
  //TODO
  return getModelValue( n );
}

void CegInstantiation::registerMeasuredType( TypeNode tn ) {
  std::map< TypeNode, Node >::iterator it = d_uf_measure.find( tn );
  if( it==d_uf_measure.end() ){
    if( tn.isDatatype() ){
      TypeNode op_tn = NodeManager::currentNM()->mkFunctionType( tn, NodeManager::currentNM()->integerType() );
      Node op = NodeManager::currentNM()->mkSkolem( "tsize", op_tn, "was created by ceg instantiation to enforce fairness." );
      d_uf_measure[tn] = op;
    }
  }
}

Node CegInstantiation::getSizeTerm( Node n, TypeNode tn, std::vector< Node >& lems ) {
  std::map< Node, Node >::iterator itt = d_size_term.find( n );
  if( itt==d_size_term.end() ){
    registerMeasuredType( tn );
    Node sn = NodeManager::currentNM()->mkNode( APPLY_UF, d_uf_measure[tn], n );
    lems.push_back( NodeManager::currentNM()->mkNode( LEQ, NodeManager::currentNM()->mkConst( Rational(0) ), sn ) );
    d_size_term[n] = sn;
    return sn;
  }else{
    return itt->second;
  }
}

void CegInstantiation::getMeasureLemmas( Node n, Node v, std::vector< Node >& lems ) {
  Trace("cegqi-lemma-debug") << "Get measure lemma " << n << " " << v << std::endl;
  Assert( n.getType()==v.getType() );
  TypeNode tn = n.getType();
  if( tn.isDatatype() ){
    Assert( v.getKind()==APPLY_CONSTRUCTOR );
    const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
    int index = Datatype::indexOf( v.getOperator().toExpr() );
    std::map< int, Node >::iterator it = d_size_term_lemma[n].find( index );
    if( it==d_size_term_lemma[n].end() ){
      Node lhs = getSizeTerm( n, tn, lems );
      //add measure lemma
      std::vector< Node > sumc;
      for( unsigned j=0; j<dt[index].getNumArgs(); j++ ){
        TypeNode tnc = v[j].getType();
        if( tnc.isDatatype() ){
          Node seln = NodeManager::currentNM()->mkNode( APPLY_SELECTOR_TOTAL, Node::fromExpr( dt[index][j].getSelector() ), n );
          sumc.push_back( getSizeTerm( seln, tnc, lems ) );
        }
      }
      Node rhs;
      if( !sumc.empty() ){
        sumc.push_back( NodeManager::currentNM()->mkConst( Rational(1) ) );
        rhs = NodeManager::currentNM()->mkNode( PLUS, sumc );
      }else{
        rhs = NodeManager::currentNM()->mkConst( Rational(0) );
      }
      Node lem = lhs.eqNode( rhs );
      Node cond = NodeManager::currentNM()->mkNode( APPLY_TESTER, Node::fromExpr( dt[index].getTester() ), n );
      lem = NodeManager::currentNM()->mkNode( OR, cond.negate(), lem );

      d_size_term_lemma[n][index] = lem;
      Trace("cegqi-lemma-debug") << "...constructed lemma " << lem << std::endl;
      lems.push_back( lem );
      //return;
    }
    //get lemmas for children
    for( unsigned i=0; i<v.getNumChildren(); i++ ){
      Node nn = NodeManager::currentNM()->mkNode( APPLY_SELECTOR_TOTAL, Node::fromExpr( dt[index][i].getSelector() ), n );
      getMeasureLemmas( nn, v[i], lems );
    }

  }
}

}