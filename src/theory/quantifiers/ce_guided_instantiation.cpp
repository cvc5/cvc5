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

CegInstantiation::CegConjecture::CegConjecture() {
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

CegInstantiation::CegInstantiation( QuantifiersEngine * qe, context::Context* c ) : QuantifiersModule( qe ), d_conj_active( c, false ), d_conj_infeasible( c, false ), d_guard_assertions( c ) {

}

bool CegInstantiation::needsCheck( Theory::Effort e ) {
  return e>=Theory::EFFORT_LAST_CALL;
}

void CegInstantiation::check( Theory::Effort e, unsigned quant_e ) {
  if( quant_e==QuantifiersEngine::QEFFORT_STANDARD ){
    Trace("cegqi-engine") << "---Countexample Guided Instantiation Engine---" << std::endl;
    Trace("cegqi-debug") << "Current conjecture status : " << d_conj_active << " " << d_conj_infeasible << std::endl;
    if( d_conj_active && !d_conj_infeasible ){
      checkCegConjecture( &d_conj );
    }
    Trace("cegqi-engine") << "Finished Countexample Guided Instantiation engine." << std::endl;
  }
}

void CegInstantiation::registerQuantifier( Node q ) {
  if( d_quantEngine->getOwner( q )==this ){
    if( !d_conj.isAssigned() ){
      Trace("cegqi") << "Register conjecture : " << q << std::endl;
      d_conj.assign( q );
      //construct base instantiation
      d_conj.d_base_inst = Rewriter::rewrite( d_quantEngine->getInstantiation( q, d_conj.d_candidates ) );
      Trace("cegqi") << "Base instantiation is : " << d_conj.d_base_inst << std::endl;
      if( getTermDatabase()->isQAttrSygus( q ) ){
        Assert( d_conj.d_base_inst.getKind()==NOT );
        Assert( d_conj.d_base_inst[0].getKind()==FORALL );
        for( unsigned j=0; j<d_conj.d_base_inst[0][0].getNumChildren(); j++ ){
          d_conj.d_inner_vars.push_back( d_conj.d_base_inst[0][0][j] );
        }
      }else if( getTermDatabase()->isQAttrSynthesis( q ) ){
        //add immediate lemma
        Node lem = NodeManager::currentNM()->mkNode( OR, d_conj.d_guard.negate(), d_conj.d_base_inst );
      }
    }else{
      Assert( d_conj.d_quant==q );
    }
  }
}

void CegInstantiation::assertNode( Node n ) {
  Trace("cegqi-debug") << "Cegqi : Assert : " << n << std::endl;
  bool pol = n.getKind()!=NOT;
  Node lit = n.getKind()==NOT ? n[0] : n;
  if( lit==d_conj.d_guard ){
    d_guard_assertions[lit] = pol;
    d_conj_infeasible = !pol;
  }
  if( lit==d_conj.d_quant ){
    d_conj_active = true;
  }
}

Node CegInstantiation::getNextDecisionRequest() {
  d_conj.initializeGuard( d_quantEngine );
  bool value;
  if( !d_quantEngine->getValuation().hasSatValue( d_conj.d_guard, value ) ) {
    if( d_guard_assertions.find( d_conj.d_guard )==d_guard_assertions.end() ){
      if( d_conj.d_guard_split.isNull() ){
        Node lem = NodeManager::currentNM()->mkNode( OR, d_conj.d_guard.negate(), d_conj.d_guard );
        d_quantEngine->getOutputChannel().lemma( lem );
      }
      Trace("cegqi-debug") << "Decide next on : " << d_conj.d_guard << "..." << std::endl;
      return d_conj.d_guard;
    }
  }
  return Node::null();
}

void CegInstantiation::checkCegConjecture( CegConjecture * conj ) {
  Node q = conj->d_quant;
  Trace("cegqi-engine-debug") << "Synthesis conjecture : " << q << std::endl;
  Trace("cegqi-engine-debug") << "  * Candidate program/output : ";
  for( unsigned i=0; i<conj->d_candidates.size(); i++ ){
    Trace("cegqi-engine-debug") << conj->d_candidates[i] << " ";
  }
  Trace("cegqi-engine-debug") << std::endl;

  if( getTermDatabase()->isQAttrSygus( q ) ){
    Trace("cegqi-engine-debug") << "  * Values are : ";
    bool success = true;
    std::vector< Node > model_values;
    for( unsigned i=0; i<conj->d_candidates.size(); i++ ){
      Node v = getModelValue( conj->d_candidates[i] );
      model_values.push_back( v );
      Trace("cegqi-engine-debug") << v << " ";
      if( v.isNull() ){
        success = false;
      }
    }
    Trace("cegqi-engine-debug") << std::endl;

    if( success ){
      //must get a counterexample to the value of the current candidate
      Node inst = conj->d_base_inst.substitute( conj->d_candidates.begin(), conj->d_candidates.end(), model_values.begin(), model_values.end() );
      inst = Rewriter::rewrite( inst );
      //body should be an existential
      Assert( inst.getKind()==NOT );
      Assert( inst[0].getKind()==FORALL );
      //immediately skolemize
      Node inst_sk = getTermDatabase()->getSkolemizedBody( inst[0] );
      Trace("cegqi-lemma") << "Counterexample lemma : " << inst_sk << std::endl;
      d_quantEngine->addLemma( NodeManager::currentNM()->mkNode( OR, q.negate(), inst_sk ) );

      //candidate refinement : the next candidate must satisfy the counterexample found for the current model of the candidate
      Assert( conj->d_inner_vars.size()==getTermDatabase()->d_skolem_constants[inst[0]].size() );
      Node inst_ce_refine = conj->d_base_inst[0][1].substitute( conj->d_inner_vars.begin(), conj->d_inner_vars.end(),
                                                                getTermDatabase()->d_skolem_constants[inst[0]].begin(), getTermDatabase()->d_skolem_constants[inst[0]].end() );
      Node lem = NodeManager::currentNM()->mkNode( OR, conj->d_guard.negate(), inst_ce_refine.negate() );
      Trace("cegqi-lemma") << "Candidate refinement lemma : " << lem << std::endl;
      d_quantEngine->addLemma( lem );
    }

  }else if( getTermDatabase()->isQAttrSynthesis( q ) ){
    std::vector< Node > model_terms;
    for( unsigned i=0; i<conj->d_candidates.size(); i++ ){
      Node t = getModelTerm( conj->d_candidates[i] );
      model_terms.push_back( t );
    }
    d_quantEngine->addInstantiation( q, model_terms, false );
  }
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
  return getModelValue( n );
}

}