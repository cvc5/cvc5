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
    qe->getValuation().ensureLiteral( d_guard );
    qe->getOutputChannel().requirePhase( d_guard, true );
  }
}

Node CegInstantiation::CegConjecture::getLiteral( QuantifiersEngine * qe, int i ) {
  std::map< int, Node >::iterator it = d_lits.find( i );
  if( it==d_lits.end() ){
    Node lit = NodeManager::currentNM()->mkNode( LEQ, d_measure_term, NodeManager::currentNM()->mkConst( Rational( i + d_measure_term_size ) ) );
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

CegInstantiation::CegInstantiation( QuantifiersEngine * qe, context::Context* c ) : QuantifiersModule( qe ){
  d_conj = new CegConjecture( d_quantEngine->getSatContext() );
}

bool CegInstantiation::needsCheck( Theory::Effort e ) {
  return e>=Theory::EFFORT_LAST_CALL;
}

void CegInstantiation::check( Theory::Effort e, unsigned quant_e ) {
  if( quant_e==QuantifiersEngine::QEFFORT_STANDARD ){
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
      std::vector< Node > mc;
      for( unsigned j=0; j<d_conj->d_candidates.size(); j++ ){
        TypeNode tn = d_conj->d_candidates[j].getType();
        registerMeasuredType( tn );
        std::map< TypeNode, Node >::iterator it = d_uf_measure.find( tn );
        if( it!=d_uf_measure.end() ){
          mc.push_back( NodeManager::currentNM()->mkNode( APPLY_UF, it->second, d_conj->d_candidates[j] ) );
        }
      }
      if( !mc.empty() ){
        d_conj->d_measure_term = mc.size()==1 ? mc[0] : NodeManager::currentNM()->mkNode( PLUS, mc );
        d_conj->d_measure_term_size = mc.size();
        Trace("cegqi") << "Measure term is : " << d_conj->d_measure_term << std::endl;
        //Node ax = NodeManager::currentNM()->mkNode( LEQ, NodeManager::currentNM()->mkConst( Rational(0) ), d_conj->d_measure_term );
        //ax = Rewriter::rewrite( ax );
        //Trace("cegqi-lemma") << "Fairness non-negative axiom : " << ax << std::endl;
        //d_quantEngine->getOutputChannel().lemma( ax );
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
  if( d_conj->isAssigned() ){
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

  if( conj->d_ce_sk.empty() ){
    Trace("cegqi-engine") << "  *** Check candidate phase..." << std::endl;
    if( getTermDatabase()->isQAttrSygus( q ) ){

      std::vector< Node > model_values;
      if( getModelValues( conj->d_candidates, model_values ) ){
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
  //return d_quantEngine->getTheoryEngine()->getModelValue( n );
  TypeNode tn = n.getType();
  if( getEqualityEngine()->hasTerm( n ) ){
    Node r = getRepresentative( n );
    Node v;
    eq::EqClassIterator eqc_i = eq::EqClassIterator( r, getEqualityEngine() );
    while( !eqc_i.isFinished() ){
      TNode nn = (*eqc_i);
      if( nn.isConst() ){
        Trace("cegqi-mv") << "..constant : " << nn << std::endl;
        return nn;
      }else if( nn.getKind()==APPLY_CONSTRUCTOR ){
        v = nn;
      }
      ++eqc_i;
    }
    if( !v.isNull() ){
      std::vector< Node > children;
      if( v.hasOperator() ){
        children.push_back( v.getOperator() );
      }
      for( unsigned i=0; i<v.getNumChildren(); i++ ){
        children.push_back( getModelValue( v[i] ) );
      }
      Node vv = NodeManager::currentNM()->mkNode( v.getKind(), children );
      Trace("cegqi-mv") << "...value : " << vv << std::endl;
      return vv;
    }
  }
  Node e = getTermDatabase()->getEnumerateTerm( tn, 0 );
  Trace("cegqi-mv") << "...enumerate : " << e << std::endl;
  return e;
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
      //cycle through constructors
      const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
      for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
        Node x = NodeManager::currentNM()->mkBoundVar( tn );
        Node cond = NodeManager::currentNM()->mkNode( APPLY_TESTER, Node::fromExpr( dt[i].getTester() ), x ).negate();

        std::vector< Node > sumc;
        sumc.push_back( NodeManager::currentNM()->mkConst( Rational(1) ) );
        for( unsigned j=0; j<dt[i].getNumArgs(); j++ ){
          TypeNode tnc = TypeNode::fromType( ((SelectorType)dt[i][j].getSelector().getType()).getRangeType() );
          if( tnc.isDatatype() ){
            registerMeasuredType( tnc );
            sumc.push_back( NodeManager::currentNM()->mkNode( APPLY_UF, d_uf_measure[tnc],
                                                              NodeManager::currentNM()->mkNode( APPLY_SELECTOR_TOTAL, dt[i][j].getSelector(), x ) ) );
          }
        }
        Node sum = sumc.size()==1 ? sumc[0] : NodeManager::currentNM()->mkNode( PLUS, sumc );
        Node eq = NodeManager::currentNM()->mkNode( EQUAL, NodeManager::currentNM()->mkNode( APPLY_UF, d_uf_measure[tn], x ), sum );

        Node ax = NodeManager::currentNM()->mkNode( FORALL, NodeManager::currentNM()->mkNode( BOUND_VAR_LIST, x ),
                                                            NodeManager::currentNM()->mkNode( OR, cond, eq ) );
        ax = Rewriter::rewrite( ax );
        Trace("cegqi-lemma") << "Fairness axiom : " << ax << std::endl;
        d_quantEngine->getOutputChannel().lemma( ax );
      }
      //all are non-negative
      Node x = NodeManager::currentNM()->mkBoundVar( tn );
      Node ax = NodeManager::currentNM()->mkNode( FORALL, NodeManager::currentNM()->mkNode( BOUND_VAR_LIST, x ),
                                                          NodeManager::currentNM()->mkNode( LEQ, NodeManager::currentNM()->mkConst( Rational(0) ),
                                                                                                 NodeManager::currentNM()->mkNode( APPLY_UF, d_uf_measure[tn], x ) ) );
      ax = Rewriter::rewrite( ax );
      Trace("cegqi-lemma") << "Fairness non-negative axiom : " << ax << std::endl;
      d_quantEngine->getOutputChannel().lemma( ax );
    }
  }
}

}