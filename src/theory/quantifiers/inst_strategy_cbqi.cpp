/*********************                                                        */
/*! \file inst_strategy_cbqi.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of cbqi instantiation strategies
 **/

#include "theory/quantifiers/inst_strategy_cbqi.h"
#include "theory/arith/theory_arith.h"
#include "theory/arith/partial_model.h"
#include "theory/arith/theory_arith_private.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers/options.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/first_order_model.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::theory::arith;
using namespace CVC4::theory::datatypes;

#define ARITH_INSTANTIATOR_USE_MINUS_DELTA

InstStrategySimplex::InstStrategySimplex( TheoryArith* th, QuantifiersEngine* ie ) :
    InstStrategy( ie ), d_th( th ), d_counter( 0 ){
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
  Debug("quant-arith-debug") << std::endl;
  debugPrint( "quant-arith-debug" );
  d_counter++;
}

void InstStrategySimplex::addTermToRow( Node i, ArithVar x, Node n, NodeBuilder<>& t ){
  if( n.getKind()==MULT ){
    if( TermDb::hasInstConstAttr(n[1]) ){
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

int InstStrategySimplex::process( Node f, Theory::Effort effort, int e ){
  if( e<2 ){
    return STATUS_UNFINISHED;
  }else if( e==2 ){
    if( d_quantActive.find( f )!=d_quantActive.end() ){
      //the point instantiation
      InstMatch m_point( f );
      bool m_point_valid = true;
      int lem = 0;
      //scan over all instantiation rows
      for( int i=0; i<d_quantEngine->getTermDatabase()->getNumInstantiationConstants( f ); i++ ){
        Node ic = d_quantEngine->getTermDatabase()->getInstantiationConstant( f, i );
        Debug("quant-arith-simplex") << "InstStrategySimplex check " << ic << ", rows = " << d_instRows[ic].size() << std::endl;
        for( int j=0; j<(int)d_instRows[ic].size(); j++ ){
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
  return STATUS_UNKNOWN;
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
  
  for( int i=0; i<(int)d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
    Node f = d_quantEngine->getModel()->getAssertedQuantifier( i );
    Debug(c) << f << std::endl;
    Debug(c) << "   Inst constants: ";
    for( int i=0; i<(int)d_quantEngine->getTermDatabase()->getNumInstantiationConstants( f ); i++ ){
      if( i>0 ){
        Debug( c ) << ", ";
      }
      Debug( c ) << d_quantEngine->getTermDatabase()->getInstantiationConstant( f, i );
    }
    Debug(c) << std::endl;
    for( int j=0; j<d_quantEngine->getTermDatabase()->getNumInstantiationConstants( f ); j++ ){
      Node ic = d_quantEngine->getTermDatabase()->getInstantiationConstant( f, j );
      Debug(c) << "   Instantiation rows for " << ic << " : ";
      for( int i=0; i<(int)d_instRows[ic].size(); i++ ){
        if( i>0 ){
          Debug(c) << ", ";
        }
        Debug(c) << d_instRows[ic][i];
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
    ++(d_quantEngine->getInstantiationEngine()->d_statistics.d_instantiations_cbqi_arith);
    return true;
  }else{
#ifdef ARITH_INSTANTIATOR_USE_MINUS_DELTA
    //otherwise try -delta
    if( doInstantiation2( f, ic, term, x, m, var, true ) ){
      ++(d_quantEngine->getInstantiationEngine()->d_statistics.d_instantiations_cbqi_arith_minus);
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



bool CegqiOutputInstStrategy::addInstantiation( std::vector< Node >& subs, std::vector< int >& subs_typ ) {
  return d_out->addInstantiation( subs, subs_typ );
}

bool CegqiOutputInstStrategy::isEligibleForInstantiation( Node n ) {
  return d_out->isEligibleForInstantiation( n );
}

bool CegqiOutputInstStrategy::addLemma( Node lem ) {
  return d_out->addLemma( lem );
}


InstStrategyCegqi::InstStrategyCegqi( QuantifiersEngine * qe ) : InstStrategy( qe ) {
  d_out = new CegqiOutputInstStrategy( this );
}

void InstStrategyCegqi::processResetInstantiationRound( Theory::Effort effort ) {
  d_check_delta_lemma = true;
}

int InstStrategyCegqi::process( Node f, Theory::Effort effort, int e ) {
  if( e<2 ){
    return STATUS_UNFINISHED;
  }else if( e==2 ){
    CegInstantiator * cinst;
    std::map< Node, CegInstantiator * >::iterator it = d_cinst.find( f );
    if( it==d_cinst.end() ){
      cinst = new CegInstantiator( d_quantEngine, d_out );
      if( d_n_delta.isNull() ){
        d_n_delta = NodeManager::currentNM()->mkSkolem( "delta", NodeManager::currentNM()->realType(), "delta for cegqi inst strategy" );
        Node delta_lem = NodeManager::currentNM()->mkNode( GT, d_n_delta, NodeManager::currentNM()->mkConst( Rational( 0 ) ) );
        d_quantEngine->getOutputChannel().lemma( delta_lem );
      }
      cinst->d_n_delta = d_n_delta;
      for( int i=0; i<d_quantEngine->getTermDatabase()->getNumInstantiationConstants( f ); i++ ){
        cinst->d_vars.push_back( d_quantEngine->getTermDatabase()->getInstantiationConstant( f, i ) );
      }
      d_cinst[f] = cinst;
    }else{
      cinst = it->second;
    }
    if( d_check_delta_lemma ){
      Trace("inst-alg") << "-> Get delta lemmas for cegqi..." << std::endl; 
      d_check_delta_lemma = false;
      std::vector< Node > dlemmas;
      cinst->getDeltaLemmas( dlemmas );
      Trace("inst-alg") << "...got " << dlemmas.size() << " delta lemmas." << std::endl; 
      if( !dlemmas.empty() ){
        bool addedLemma = false;
        for( unsigned i=0; i<dlemmas.size(); i++ ){
          if( addLemma( dlemmas[i] ) ){
            addedLemma = true;
          }
        }
        if( addedLemma ){
          return STATUS_UNKNOWN;
        }
      }
    }
    Trace("inst-alg") << "-> Run cegqi for " << f << std::endl;
    d_curr_quant = f;
    cinst->check();
    d_curr_quant = Node::null();
  }
  return STATUS_UNKNOWN;
}

bool InstStrategyCegqi::addInstantiation( std::vector< Node >& subs, std::vector< int >& subs_typ ) {
  Assert( !d_curr_quant.isNull() );
  /*
  std::stringstream siss;
  if( Trace.isOn("inst-cegqi") || Trace.isOn("inst-cegqi-debug") ){
    for( unsigned j=0; j<d_single_inv_sk.size(); j++ ){
      Node v = d_single_inv_map_to_prog[d_single_inv[0][j]];
      siss << "    * " << v;
      siss << " (" << d_single_inv_sk[j] << ")";
      siss << " -> " << ( subs_typ[j]==9 ? "M:" : "") << subs[j] << std::endl;
    }
  }  
  */
  return d_quantEngine->addInstantiation( d_curr_quant, subs, false );
}

bool InstStrategyCegqi::addLemma( Node lem ) {
  return d_quantEngine->addLemma( lem );
}

bool InstStrategyCegqi::isEligibleForInstantiation( Node n ) {
  if( n.getKind()==INST_CONSTANT ){
    //only legal if current quantified formula contains n
    return TermDb::containsTerm( d_curr_quant, n );
  }else{
    return true;
  }
} 













