/*********************                                                        */
/*! \file inst_strategy_cbqi.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of counterexample-guided quantifier instantiation strategies
 **/
#include "theory/quantifiers/inst_strategy_cbqi.h"

#include "options/quantifiers_options.h"
#include "smt/ite_removal.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/theory_arith.h"
#include "theory/arith/theory_arith_private.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/trigger.h"
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
  : QuantifiersModule( qe ), d_added_cbqi_lemma( qe->getUserContext() )
//, d_added_inst( qe->getUserContext() )
{
}

InstStrategyCbqi::~InstStrategyCbqi() throw(){}

bool InstStrategyCbqi::needsCheck( Theory::Effort e ) {
  return e>=Theory::EFFORT_LAST_CALL;
}

unsigned InstStrategyCbqi::needsModel( Theory::Effort e ) {
  for( unsigned i=0; i<d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
    Node q = d_quantEngine->getModel()->getAssertedQuantifier( i );
    if( doCbqi( q ) && d_quantEngine->getModel()->isQuantifierActive( q ) ){
      return QuantifiersEngine::QEFFORT_STANDARD;
    }
  }
  return QuantifiersEngine::QEFFORT_NONE;
}

void InstStrategyCbqi::reset_round( Theory::Effort effort ) {
  d_cbqi_set_quant_inactive = false;
  d_incomplete_check = false;
  //check if any cbqi lemma has not been added yet
  for( unsigned i=0; i<d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
    Node q = d_quantEngine->getModel()->getAssertedQuantifier( i );
    //it is not active if it corresponds to a rewrite rule: we will process in rewrite engine
    if( doCbqi( q ) ){
      if( !hasAddedCbqiLemma( q ) ){
        d_added_cbqi_lemma.insert( q );
        Trace("cbqi") << "Do cbqi for " << q << std::endl;
        //add cbqi lemma
        //get the counterexample literal
        Node ceLit = d_quantEngine->getTermDatabase()->getCounterexampleLiteral( q );
        Node ceBody = d_quantEngine->getTermDatabase()->getInstConstantBody( q );
        if( !ceBody.isNull() ){
          //add counterexample lemma
          Node lem = NodeManager::currentNM()->mkNode( OR, ceLit.negate(), ceBody.negate() );
          //require any decision on cel to be phase=true
          d_quantEngine->addRequirePhase( ceLit, true );
          Debug("cbqi-debug") << "Require phase " << ceLit << " = true." << std::endl;
          //add counterexample lemma
          lem = Rewriter::rewrite( lem );
          Trace("cbqi") << "Counterexample lemma : " << lem << std::endl;
          registerCounterexampleLemma( q, lem );
        }
      //set inactive the quantified formulas whose CE literals are asserted false
      }else if( d_quantEngine->getModel()->isQuantifierActive( q ) ){
        Debug("cbqi-debug") << "Check quantified formula " << q << "..." << std::endl;
        Node cel = d_quantEngine->getTermDatabase()->getCounterexampleLiteral( q );
        bool value;
        if( d_quantEngine->getValuation().hasSatValue( cel, value ) ){
          Debug("cbqi-debug") << "...CE Literal has value " << value << std::endl;
          if( !value ){
            if( d_quantEngine->getValuation().isDecision( cel ) ){
              Trace("cbqi-warn") << "CBQI WARNING: Bad decision on CE Literal." << std::endl;
            }else{
              d_quantEngine->getModel()->setQuantifierActive( q, false );
              d_cbqi_set_quant_inactive = true;
            }
          }
        }else{
          Debug("cbqi-debug") << "...CE Literal does not have value " << std::endl;
        }
      }
    }
  }
  processResetInstantiationRound( effort );
}

void InstStrategyCbqi::check( Theory::Effort e, unsigned quant_e ) {
  if( quant_e==QuantifiersEngine::QEFFORT_STANDARD ){
    Assert( !d_quantEngine->inConflict() );
    double clSet = 0;
    if( Trace.isOn("cbqi-engine") ){
      clSet = double(clock())/double(CLOCKS_PER_SEC);
      Trace("cbqi-engine") << "---Cbqi Engine Round, effort = " << e << "---" << std::endl;
    }
    unsigned lastWaiting = d_quantEngine->getNumLemmasWaiting();
    for( int ee=0; ee<=1; ee++ ){
      for( unsigned i=0; i<d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
        Node q = d_quantEngine->getModel()->getAssertedQuantifier( i );
        if( doCbqi( q ) && d_quantEngine->getModel()->isQuantifierActive( q ) ){
          process( q, e, ee );
          if( d_quantEngine->inConflict() ){
            break;
          }
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

void InstStrategyCbqi::preRegisterQuantifier( Node q ) {
  if( d_quantEngine->getOwner( q )==NULL && doCbqi( q ) ){
    if( !options::cbqiAll() && !options::cbqiSplx() ){
      //take full ownership of the quantified formula
      d_quantEngine->setOwner( q, this );
    }
  }
}

void InstStrategyCbqi::registerQuantifier( Node q ) {

}

void InstStrategyCbqi::registerCounterexampleLemma( Node q, Node lem ){
  Trace("cbqi-debug") << "Counterexample lemma  : " << lem << std::endl;
  d_quantEngine->addLemma( lem, false );
}

bool InstStrategyCbqi::hasNonCbqiOperator( Node n, std::map< Node, bool >& visited ){
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    if( n.getKind()!=BOUND_VARIABLE && TermDb::hasBoundVarAttr( n ) ){
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
bool InstStrategyCbqi::hasNonCbqiVariable( Node q ){
  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
    TypeNode tn = q[0][i].getType();
    if( !tn.isInteger() && !tn.isReal() && !tn.isBoolean() ){
      if( options::cbqiSplx() ){
        return true;
      }else{
        //datatypes supported in new implementation
        if( !tn.isDatatype() ){
          return true;
        }
      }
    }
  }
  return false;
}

bool InstStrategyCbqi::doCbqi( Node q ){
  std::map< Node, bool >::iterator it = d_do_cbqi.find( q );
  if( it==d_do_cbqi.end() ){
    bool ret = false;
    if( d_quantEngine->getTermDatabase()->isQAttrQuantElim( q ) ){
      ret = true;
    }else{
      //if has an instantiation pattern, don't do it
      if( q.getNumChildren()==3 && options::eMatching() && options::userPatternsQuant()!=USER_PAT_MODE_IGNORE ){
        ret = false;
      }else{
        if( options::cbqiAll() ){
          ret = true;
        }else{
          //if quantifier has a non-arithmetic variable, then do not use cbqi
          //if quantifier has an APPLY_UF term, then do not use cbqi
          //Node cb = d_quantEngine->getTermDatabase()->getInstConstantBody( q );
          std::map< Node, bool > visited;
          ret = !hasNonCbqiVariable( q ) && !hasNonCbqiOperator( q[1], visited );
        }
      }
    }
    Trace("cbqi") << "doCbqi " << q << " returned " << ret << std::endl;
    d_do_cbqi[q] = ret;
    return ret;
  }else{
    return it->second;
  }
}

Node InstStrategyCbqi::getNextDecisionRequest(){
  // all counterexample literals that are not asserted
  for( unsigned i=0; i<d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
    Node q = d_quantEngine->getModel()->getAssertedQuantifier( i );
    if( hasAddedCbqiLemma( q ) ){
      Node cel = d_quantEngine->getTermDatabase()->getCounterexampleLiteral( q );
      bool value;
      if( !d_quantEngine->getValuation().hasSatValue( cel, value ) ){
        Trace("cbqi-debug2") << "CBQI: get next decision " << cel << std::endl;
        return cel;
      }
    }
  }
  return Node::null();
}




//old implementation

InstStrategySimplex::InstStrategySimplex( TheoryArith* th, QuantifiersEngine* ie ) : InstStrategyCbqi( ie ), d_th( th ), d_counter( 0 ){
  d_negOne = NodeManager::currentNM()->mkConst( Rational(-1) );
  d_zero = NodeManager::currentNM()->mkConst( Rational(0) );
}

void getInstantiationConstants( Node n, std::vector< Node >& ics ){
  if( n.getKind()==INST_CONSTANT ){
    if( std::find( ics.begin(), ics.end(), n )==ics.end() ){
      ics.push_back( n );
    }
  }else{
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      getInstantiationConstants( n[i], ics );
    }
  }
}


void InstStrategySimplex::processResetInstantiationRound( Theory::Effort effort ){
  Debug("quant-arith") << "Setting up simplex for instantiator... " << std::endl;
  d_quantActive.clear();
  d_instRows.clear();
  d_tableaux_term.clear();
  d_tableaux.clear();
  d_ceTableaux.clear();
  //search for instantiation rows in simplex tableaux
  ArithVariables& avnm = d_th->d_internal->d_partialModel;
  ArithVariables::var_iterator vi, vend;
  for(vi = avnm.var_begin(), vend = avnm.var_end(); vi != vend; ++vi ){
    ArithVar x = *vi;
    Node n = avnm.asNode(x);

    //collect instantiation constants
    std::vector< Node > ics;
    getInstantiationConstants( n, ics );
    for( unsigned i=0; i<ics.size(); i++ ){
      NodeBuilder<> t(kind::PLUS);
      if( n.getKind()==PLUS ){
        for( int j=0; j<(int)n.getNumChildren(); j++ ){
          addTermToRow( ics[i], x, n[j], t );
        }
      }else{
        addTermToRow( ics[i], x, n, t );
      }
      d_instRows[ics[i]].push_back( x );
      //this theory has constraints from f
      Node f = TermDb::getInstConstAttr(ics[i]);
      Debug("quant-arith") << "Has constraints from " << f << std::endl;
      //set that we should process it
      d_quantActive[ f ] = true;
      //set tableaux term
      if( t.getNumChildren()==0 ){
        d_tableaux_term[ics[i]][x] = d_zero;
      }else if( t.getNumChildren()==1 ){
        d_tableaux_term[ics[i]][x] = t.getChild( 0 );
      }else{
        d_tableaux_term[ics[i]][x] = t;
      }
    }
  }
  //print debug
  if( Debug.isOn("quant-arith-debug") ){
    Debug("quant-arith-debug") << std::endl;
    debugPrint( "quant-arith-debug" );
  }
  d_counter++;
}

void InstStrategySimplex::addTermToRow( Node i, ArithVar x, Node n, NodeBuilder<>& t ){
  if( n.getKind()==MULT ){
    if( TermDb::hasInstConstAttr(n[1]) && n[0].getKind()==CONST_RATIONAL ){
      if( n[1]==i ){
        d_ceTableaux[i][x][ n[1] ] = n[0];
      }else{
        d_tableaux_ce_term[i][x][ n[1] ] = n[0];
      }
    }else{
      d_tableaux[i][x][ n[1] ] = n[0];
      t << n;
    }
  }else{
    if( TermDb::hasInstConstAttr(n) ){
      if( n==i ){
        d_ceTableaux[i][x][ n ] = Node::null();
      }else{
        d_tableaux_ce_term[i][x][ n ] = NodeManager::currentNM()->mkConst( Rational(1) );
      }
    }else{
      d_tableaux[i][x][ n ] = NodeManager::currentNM()->mkConst( Rational(1) );
      t << n;
    }
  }
}

void InstStrategySimplex::process( Node f, Theory::Effort effort, int e ){
  if( e==0 ){
    if( d_quantActive.find( f )!=d_quantActive.end() ){
      //the point instantiation
      InstMatch m_point( f );
      bool m_point_valid = true;
      int lem = 0;
      //scan over all instantiation rows
      for( unsigned i=0; i<d_quantEngine->getTermDatabase()->getNumInstantiationConstants( f ); i++ ){
        Node ic = d_quantEngine->getTermDatabase()->getInstantiationConstant( f, i );
        Debug("quant-arith-simplex") << "InstStrategySimplex check " << ic << ", rows = " << d_instRows[ic].size() << std::endl;
        for( unsigned j=0; j<d_instRows[ic].size(); j++ ){
          ArithVar x = d_instRows[ic][j];
          if( !d_ceTableaux[ic][x].empty() ){
            if( Debug.isOn("quant-arith-simplex") ){
              Debug("quant-arith-simplex") << "--- Check row " << ic << " " << x << std::endl;
              Debug("quant-arith-simplex") << "  ";
              for( std::map< Node, Node >::iterator it = d_ceTableaux[ic][x].begin(); it != d_ceTableaux[ic][x].end(); ++it ){
                if( it!=d_ceTableaux[ic][x].begin() ){ Debug("quant-arith-simplex") << " + "; }
                Debug("quant-arith-simplex") << it->first << " * " << it->second;
              }
              Debug("quant-arith-simplex") << " = ";
              Node v = getTableauxValue( x, false );
              Debug("quant-arith-simplex") << v << std::endl;
              Debug("quant-arith-simplex") << "  term : " << d_tableaux_term[ic][x] << std::endl;
              Debug("quant-arith-simplex") << "  ce-term : ";
              for( std::map< Node, Node >::iterator it = d_tableaux_ce_term[ic][x].begin(); it != d_tableaux_ce_term[ic][x].end(); it++ ){
                if( it!=d_tableaux_ce_term[ic][x].begin() ){ Debug("quant-arith-simplex") << " + "; }
                Debug("quant-arith-simplex") << it->first << " * " << it->second;
              }
              Debug("quant-arith-simplex") << std::endl;
            }
            //instantiation row will be A*e + B*t = beta,
            // where e is a vector of terms , and t is vector of ground terms.
            // Say one term in A*e is coeff*e_i, where e_i is an instantiation constant
            // We will construct the term ( beta - B*t)/coeff to use for e_i.
            InstMatch m( f );
            for( unsigned k=0; k<f[0].getNumChildren(); k++ ){
              if( f[0][k].getType().isInteger() ){
                m.setValue( k, d_zero );
              }
            }
            //By default, choose the first instantiation constant to be e_i.
            Node var = d_ceTableaux[ic][x].begin()->first;
            //if it is integer, we need to find variable with coefficent +/- 1
            if( var.getType().isInteger() ){
              std::map< Node, Node >::iterator it = d_ceTableaux[ic][x].begin();
              while( !var.isNull() && !d_ceTableaux[ic][x][var].isNull() && d_ceTableaux[ic][x][var]!=d_negOne ){
                ++it;
                if( it==d_ceTableaux[ic][x].end() ){
                  var = Node::null();
                }else{
                  var = it->first;
                }
              }
              //Otherwise, try one that divides all ground term coefficients?
              //  Might be futile, if rewrite ensures gcd of coeffs is 1.
            }
            if( !var.isNull() ){
              //add to point instantiation if applicable
              if( d_tableaux_ce_term[ic][x].empty() && d_tableaux_term[ic][x]==d_zero ){
                Debug("quant-arith-simplex") << "*** Row contributes to point instantiation." << std::endl;
                Node v = getTableauxValue( x, false );
                if( !var.getType().isInteger() || v.getType().isInteger() ){
                  m_point.setValue( i, v );
                }else{
                  m_point_valid = false;
                }
              }
              Debug("quant-arith-simplex") << "Instantiate with var " << var << std::endl;
              if( doInstantiation( f, ic, d_tableaux_term[ic][x], x, m, var ) ){
                lem++;
              }
            }else{
              Debug("quant-arith-simplex") << "Could not find var." << std::endl;
            }
          }
        }
      }
      if( lem==0 && m_point_valid ){
        if( d_quantEngine->addInstantiation( f, m_point ) ){
          Debug("quant-arith-simplex") << "...added point instantiation." << std::endl;
        }
      }
    }
  }
}


void InstStrategySimplex::debugPrint( const char* c ){
  ArithVariables& avnm = d_th->d_internal->d_partialModel;
  ArithVariables::var_iterator vi, vend;
  for(vi = avnm.var_begin(), vend = avnm.var_end(); vi != vend; ++vi ){
    ArithVar x = *vi;
    Node n = avnm.asNode(x);
    //if( ((TheoryArith*)getTheory())->d_partialModel.hasEitherBound( x ) ){
      Debug(c) << x << " : " << n << ", bounds = ";
      if( d_th->d_internal->d_partialModel.hasLowerBound( x ) ){
        Debug(c) << d_th->d_internal->d_partialModel.getLowerBound( x );
      }else{
        Debug(c) << "-infty";
      }
      Debug(c) << " <= ";
      Debug(c) << d_th->d_internal->d_partialModel.getAssignment( x );
      Debug(c) << " <= ";
      if( d_th->d_internal->d_partialModel.hasUpperBound( x ) ){
        Debug(c) << d_th->d_internal->d_partialModel.getUpperBound( x );
      }else{
        Debug(c) << "+infty";
      }
      Debug(c) << std::endl;
      //Debug(c) << "   Term = " << d_tableaux_term[x] << std::endl;
      //Debug(c) << "   ";
      //for( std::map< Node, Node >::iterator it2 = d_tableaux[x].begin(); it2 != d_tableaux[x].end(); ++it2 ){
      //  Debug(c) << "( " << it2->first << ", " << it2->second << " ) ";
      //}
      //for( std::map< Node, Node >::iterator it2 = d_ceTableaux[x].begin(); it2 != d_ceTableaux[x].end(); ++it2 ){
      //  Debug(c) << "(CE)( " << it2->first << ", " << it2->second << " ) ";
      //}
      //for( std::map< Node, Node >::iterator it2 = d_tableaux_ce_term[x].begin(); it2 != d_tableaux_ce_term[x].end(); ++it2 ){
      //  Debug(c) << "(CE-term)( " << it2->first << ", " << it2->second << " ) ";
      //}
      //Debug(c) << std::endl;
    //}
  }
  Debug(c) << std::endl;

  for( unsigned i=0; i<d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
    Node f = d_quantEngine->getModel()->getAssertedQuantifier( i );
    Debug(c) << f << std::endl;
    Debug(c) << "   Inst constants: ";
    for( unsigned j=0; j<d_quantEngine->getTermDatabase()->getNumInstantiationConstants( f ); i++ ){
      if( j>0 ){
        Debug( c ) << ", ";
      }
      Debug( c ) << d_quantEngine->getTermDatabase()->getInstantiationConstant( f, i );
    }
    Debug(c) << std::endl;
    for( unsigned j=0; j<d_quantEngine->getTermDatabase()->getNumInstantiationConstants( f ); j++ ){
      Node ic = d_quantEngine->getTermDatabase()->getInstantiationConstant( f, j );
      Debug(c) << "   Instantiation rows for " << ic << " : ";
      for( unsigned k=0; k<d_instRows[ic].size(); k++ ){
        if( k>0 ){
          Debug(c) << ", ";
        }
        Debug(c) << d_instRows[ic][k];
      }
      Debug(c) << std::endl;
    }
  }
}

//say instantiation row x for quantifier f is coeff*var + A*t[e] + term = beta,
// where var is an instantiation constant from f,
// t[e] is a vector of terms containing instantiation constants from f,
// and term is a ground term (c1*t1 + ... + cn*tn).
// We construct the term ( beta - term )/coeff to use as an instantiation for var.
bool InstStrategySimplex::doInstantiation( Node f, Node ic, Node term, ArithVar x, InstMatch& m, Node var ){
  //first try +delta
  if( doInstantiation2( f, ic, term, x, m, var ) ){
    ++(d_quantEngine->d_statistics.d_instantiations_cbqi_arith);
    return true;
  }else{
#ifdef ARITH_INSTANTIATOR_USE_MINUS_DELTA
    //otherwise try -delta
    if( doInstantiation2( f, ic, term, x, m, var, true ) ){
      ++(d_quantEngine->d_statistics.d_instantiations_cbqi_arith);
      return true;
    }else{
      return false;
    }
#else
    return false;
#endif
  }
}

bool InstStrategySimplex::doInstantiation2( Node f, Node ic, Node term, ArithVar x, InstMatch& m, Node var, bool minus_delta ){
  // make term ( beta - term )/coeff
  bool vIsInteger = var.getType().isInteger();
  Node beta = getTableauxValue( x, minus_delta );
  if( !vIsInteger || beta.getType().isInteger() ){
    Node instVal = NodeManager::currentNM()->mkNode( MINUS, beta, term );
    if( !d_ceTableaux[ic][x][var].isNull() ){
      if( vIsInteger ){
        Assert( d_ceTableaux[ic][x][var]==NodeManager::currentNM()->mkConst( Rational(-1) ) );
        instVal = NodeManager::currentNM()->mkNode( MULT, d_ceTableaux[ic][x][var], instVal );
      }else{
        Assert( d_ceTableaux[ic][x][var].getKind()==CONST_RATIONAL );
        Node coeff = NodeManager::currentNM()->mkConst( Rational(1) / d_ceTableaux[ic][x][var].getConst<Rational>() );
        instVal = NodeManager::currentNM()->mkNode( MULT, coeff, instVal );
      }
    }
    instVal = Rewriter::rewrite( instVal );
    //use as instantiation value for var
    int vn = var.getAttribute(InstVarNumAttribute());
    m.setValue( vn, instVal );
    Debug("quant-arith") << "Add instantiation " << m << std::endl;
    return d_quantEngine->addInstantiation( f, m );
  }else{
    return false;
  }
}
/*
Node InstStrategySimplex::getTableauxValue( Node n, bool minus_delta ){
  if( d_th->d_internal->d_partialModel.hasArithVar(n) ){
    ArithVar v = d_th->d_internal->d_partialModel.asArithVar( n );
    return getTableauxValue( v, minus_delta );
  }else{
    return NodeManager::currentNM()->mkConst( Rational(0) );
  }
}
*/
Node InstStrategySimplex::getTableauxValue( ArithVar v, bool minus_delta ){
  const Rational& delta = d_th->d_internal->d_partialModel.getDelta();
  DeltaRational drv = d_th->d_internal->d_partialModel.getAssignment( v );
  Rational qmodel = drv.substituteDelta( minus_delta ? -delta : delta );
  return mkRationalNode(qmodel);
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
}

InstStrategyCegqi::~InstStrategyCegqi() throw () {
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
      Node delta = d_quantEngine->getTermDatabase()->getVtsDelta( true, false );
      if( !delta.isNull() ){
        Trace("quant-vts-debug") << "Delta lemma for " << d_small_const << std::endl;
        Node delta_lem_ub = NodeManager::currentNM()->mkNode( LT, delta, d_small_const );
        d_quantEngine->getOutputChannel().lemma( delta_lem_ub );
      }
      std::vector< Node > inf;
      d_quantEngine->getTermDatabase()->getVtsTerms( inf, true, false, false );
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
  if( d_quantEngine->getTermDatabase()->isQAttrQuantElimPartial( d_curr_quant ) ){
    d_cbqi_set_quant_inactive = true;
    d_incomplete_check = true;
    d_quantEngine->recordInstantiationInternal( d_curr_quant, subs, false, false );
    return true;
  }else{
    //check if we need virtual term substitution (if used delta or infinity)
    bool used_vts = d_quantEngine->getTermDatabase()->containsVtsTerm( subs, false );
    if( d_quantEngine->addInstantiation( d_curr_quant, subs, false, false, used_vts ) ){
      //d_added_inst.insert( d_curr_quant );
      return true;
    }else{
      return false;
    }
  }
}

bool InstStrategyCegqi::addLemma( Node lem ) {
  return d_quantEngine->addLemma( lem );
}

bool InstStrategyCegqi::isEligibleForInstantiation( Node n ) {
  if( n.getKind()==INST_CONSTANT || n.getKind()==SKOLEM ){
    if( n.getKind()==SKOLEM && d_quantEngine->getTermDatabase()->containsVtsTerm( n ) ){
      return true;
    }else{
      //only legal if current quantified formula contains n
      return TermDb::containsTerm( d_curr_quant, n );
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
  if( options::cbqiPreRegInst() ){
    if( doCbqi( q ) ){
      //just get the instantiator
      getInstantiator( q );
    }
  }
}

void InstStrategyCegqi::registerCounterexampleLemma( Node q, Node lem ) {
  //must register with the instantiator
  //must explicitly remove ITEs so that we record dependencies
  std::vector< Node > ce_vars;
  for( unsigned i=0; i<d_quantEngine->getTermDatabase()->getNumInstantiationConstants( q ); i++ ){
    ce_vars.push_back( d_quantEngine->getTermDatabase()->getInstantiationConstant( q, i ) );
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
      it->second->presolve( it->first );
    }
  }
}
