/*********************                                                        */
/*! \file inst_strategy_cbqi.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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
}

bool InstStrategySimplex::calculateShouldProcess( Node f ){
  //DO_THIS
  return false;
}

void InstStrategySimplex::processResetInstantiationRound( Theory::Effort effort ){
  Debug("quant-arith") << "Setting up simplex for instantiator... " << std::endl;
  d_instRows.clear();
  d_tableaux_term.clear();
  d_tableaux.clear();
  d_ceTableaux.clear();
  //search for instantiation rows in simplex tableaux
  ArithVariables& avnm = d_th->d_internal->d_partialModel;
  ArithVariables::var_iterator vi, vend;
  for(vi = avnm.var_begin(), vend = avnm.var_end(); vi != vend; ++vi ){
    ArithVar x = *vi;
    if( d_th->d_internal->d_partialModel.hasEitherBound( x ) ){
      Node n = avnm.asNode(x);
      Node f;
      NodeBuilder<> t(kind::PLUS);
      if( n.getKind()==PLUS ){
        for( int i=0; i<(int)n.getNumChildren(); i++ ){
          addTermToRow( x, n[i], f, t );
        }
      }else{
        addTermToRow( x, n, f, t );
      }
      if( f!=Node::null() ){
        d_instRows[f].push_back( x );
        //this theory has constraints from f
        Debug("quant-arith") << "Has constraints from " << f << std::endl;
        //set that we should process it
        d_quantActive[ f ] = true;
        //set tableaux term
        if( t.getNumChildren()==0 ){
          d_tableaux_term[x] = NodeManager::currentNM()->mkConst( Rational(0) );
        }else if( t.getNumChildren()==1 ){
          d_tableaux_term[x] = t.getChild( 0 );
        }else{
          d_tableaux_term[x] = t;
        }
      }
    }
  }
  //print debug
  debugPrint( "quant-arith-debug" );
  d_counter++;
}

int InstStrategySimplex::process( Node f, Theory::Effort effort, int e ){
  if( e<2 ){
    return STATUS_UNFINISHED;
  }else if( e==2 ){
    //Notice() << f << std::endl;
    //Notice() << "Num inst rows = " << d_th->d_instRows[f].size() << std::endl;
    //Notice() << "Num inst constants = " << d_quantEngine->getNumInstantiationConstants( f ) << std::endl;
    Debug("quant-arith-simplex") << "InstStrategySimplex check " << f << ", rows = " << d_instRows[f].size() << std::endl;
    for( int j=0; j<(int)d_instRows[f].size(); j++ ){
      ArithVar x = d_instRows[f][j];
      if( !d_ceTableaux[x].empty() ){
        Debug("quant-arith-simplex") << "Check row " << x << std::endl;
        //instantiation row will be A*e + B*t = beta,
        // where e is a vector of terms , and t is vector of ground terms.
        // Say one term in A*e is coeff*e_i, where e_i is an instantiation constant
        // We will construct the term ( beta - B*t)/coeff to use for e_i.
        InstMatch m;
        //By default, choose the first instantiation constant to be e_i.
        Node var = d_ceTableaux[x].begin()->first;
        if( var.getType().isInteger() ){
          std::map< Node, Node >::iterator it = d_ceTableaux[x].begin();
          //try to find coefficent that is +/- 1
          while( !var.isNull() && !d_ceTableaux[x][var].isNull() && d_ceTableaux[x][var]!=d_negOne ){
            ++it;
            if( it==d_ceTableaux[x].end() ){
              var = Node::null();
            }else{
              var = it->first;
            }
          }
          //otherwise, try one that divides all ground term coefficients? DO_THIS
        }
        if( !var.isNull() ){
          Debug("quant-arith-simplex") << "Instantiate with var " << var << std::endl;
          doInstantiation( f, d_tableaux_term[x], x, m, var );
        }else{
          Debug("quant-arith-simplex") << "Could not find var." << std::endl;
        }
        ////choose a new variable based on alternation strategy
        //int index = d_counter%(int)d_th->d_ceTableaux[x].size();
        //Node var;
        //for( std::map< Node, Node >::iterator it = d_th->d_ceTableaux[x].begin(); it != d_th->d_ceTableaux[x].end(); ++it ){
        //  if( index==0 ){
        //    var = it->first;
        //    break;
        //  }
        //  index--;
        //}
        //d_th->doInstantiation( f, d_th->d_tableaux_term[x], x, &m, var );
      }
    }
  }
  return STATUS_UNKNOWN;
}


void InstStrategySimplex::addTermToRow( ArithVar x, Node n, Node& f, NodeBuilder<>& t ){
  if( n.getKind()==MULT ){
    if( n[1].hasAttribute(InstConstantAttribute()) ){
      f = n[1].getAttribute(InstConstantAttribute());
      if( n[1].getKind()==INST_CONSTANT ){
        d_ceTableaux[x][ n[1] ] = n[0];
      }else{
        d_tableaux_ce_term[x][ n[1] ] = n[0];
      }
    }else{
      d_tableaux[x][ n[1] ] = n[0];
      t << n;
    }
  }else{
    if( n.hasAttribute(InstConstantAttribute()) ){
      f = n.getAttribute(InstConstantAttribute());
      if( n.getKind()==INST_CONSTANT ){
        d_ceTableaux[x][ n ] = Node::null();
      }else{
        d_tableaux_ce_term[x][ n ] = NodeManager::currentNM()->mkConst( Rational(1) );
      }
    }else{
      d_tableaux[x][ n ] = NodeManager::currentNM()->mkConst( Rational(1) );
      t << n;
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

  for( int q=0; q<d_quantEngine->getNumQuantifiers(); q++ ){
    Node f = d_quantEngine->getQuantifier( q );
    Debug(c) << f << std::endl;
    Debug(c) << "   Inst constants: ";
    for( int i=0; i<(int)d_quantEngine->getTermDatabase()->getNumInstantiationConstants( f ); i++ ){
      if( i>0 ){
        Debug( c ) << ", ";
      }
      Debug( c ) << d_quantEngine->getTermDatabase()->getInstantiationConstant( f, i );
    }
    Debug(c) << std::endl;
    Debug(c) << "   Instantiation rows: ";
    for( int i=0; i<(int)d_instRows[f].size(); i++ ){
      if( i>0 ){
        Debug(c) << ", ";
      }
      Debug(c) << d_instRows[f][i];
    }
    Debug(c) << std::endl;
  }
}

//say instantiation row x for quantifier f is coeff*var + A*t[e] + term = beta,
// where var is an instantiation constant from f,
// t[e] is a vector of terms containing instantiation constants from f,
// and term is a ground term (c1*t1 + ... + cn*tn).
// We construct the term ( beta - term )/coeff to use as an instantiation for var.
bool InstStrategySimplex::doInstantiation( Node f, Node term, ArithVar x, InstMatch& m, Node var ){
  //first try +delta
  if( doInstantiation2( f, term, x, m, var ) ){
    ++(d_quantEngine->getInstantiationEngine()->d_statistics.d_instantiations_cbqi_arith);
    return true;
  }else{
#ifdef ARITH_INSTANTIATOR_USE_MINUS_DELTA
    //otherwise try -delta
    if( doInstantiation2( f, term, x, m, var, true ) ){
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

bool InstStrategySimplex::doInstantiation2( Node f, Node term, ArithVar x, InstMatch& m, Node var, bool minus_delta ){
  // make term ( beta - term )/coeff
  Node beta = getTableauxValue( x, minus_delta );
  Node instVal = NodeManager::currentNM()->mkNode( MINUS, beta, term );
  if( !d_ceTableaux[x][var].isNull() ){
    if( var.getType().isInteger() ){
      Assert( d_ceTableaux[x][var]==NodeManager::currentNM()->mkConst( Rational(-1) ) );
      instVal = NodeManager::currentNM()->mkNode( MULT, d_ceTableaux[x][var], instVal );
    }else{
      Node coeff = NodeManager::currentNM()->mkConst( Rational(1) / d_ceTableaux[x][var].getConst<Rational>() );
      instVal = NodeManager::currentNM()->mkNode( MULT, coeff, instVal );
    }
  }
  instVal = Rewriter::rewrite( instVal );
  //use as instantiation value for var
  m.set(var, instVal);
  Debug("quant-arith") << "Add instantiation " << m << std::endl;
  return d_quantEngine->addInstantiation( f, m );
}

Node InstStrategySimplex::getTableauxValue( Node n, bool minus_delta ){
  if( d_th->d_internal->d_partialModel.hasArithVar(n) ){
    ArithVar v = d_th->d_internal->d_partialModel.asArithVar( n );
    return getTableauxValue( v, minus_delta );
  }else{
    return NodeManager::currentNM()->mkConst( Rational(0) );
  }
}

Node InstStrategySimplex::getTableauxValue( ArithVar v, bool minus_delta ){
  const Rational& delta = d_th->d_internal->d_partialModel.getDelta();
  DeltaRational drv = d_th->d_internal->d_partialModel.getAssignment( v );
  Rational qmodel = drv.substituteDelta( minus_delta ? -delta : delta );
  return mkRationalNode(qmodel);
}


InstStrategyDatatypesValue::InstStrategyDatatypesValue( TheoryDatatypes* th, QuantifiersEngine* qe ) :
  InstStrategy( qe ), d_th( th ){

}

bool InstStrategyDatatypesValue::calculateShouldProcess( Node f ){
  //DO_THIS
  return false;
}

void InstStrategyDatatypesValue::processResetInstantiationRound( Theory::Effort effort ){

}

int InstStrategyDatatypesValue::process( Node f, Theory::Effort effort, int e ){
  Debug("quant-datatypes") << "Datatypes: Try to solve (" << e << ") for " << f << "... " << std::endl;
  if( e<2 ){
    return InstStrategy::STATUS_UNFINISHED;
  }else if( e==2 ){
    InstMatch m;
    for( int j = 0; j<(int)d_quantEngine->getTermDatabase()->getNumInstantiationConstants( f ); j++ ){
      Node i = d_quantEngine->getTermDatabase()->getInstantiationConstant( f, j );
      if( i.getType().isDatatype() ){
        Node n = getValueFor( i );
        Debug("quant-datatypes-debug") << "Value for " << i << " is " << n << std::endl;
        m.set(i,n);
      }
    }
    //d_quantEngine->addInstantiation( f, m );
  }
  return InstStrategy::STATUS_UNKNOWN;
}

Node InstStrategyDatatypesValue::getValueFor( Node n ){
  //simply get the ground value for n in the current model, if it exists,
  //  or return an arbitrary ground term otherwise
  if( !n.hasAttribute(InstConstantAttribute()) ){
    return n;
  }else{
    return n;
  }
  /*  FIXME

  Debug("quant-datatypes-debug")  << "get value for " << n << std::endl;
  if( !n.hasAttribute(InstConstantAttribute()) ){
    return n;
  }else{
    Assert( n.getType().isDatatype() );
    //check if in equivalence class with ground term
    Node rep = getRepresentative( n );
    Debug("quant-datatypes-debug") << "Rep is " << rep << std::endl;
    if( !rep.hasAttribute(InstConstantAttribute()) ){
      return rep;
    }else{
      if( !n.getType().isDatatype() ){
        return n.getType().mkGroundTerm();
      }else{
        if( n.getKind()==APPLY_CONSTRUCTOR ){
          std::vector< Node > children;
          children.push_back( n.getOperator() );
          for( int i=0; i<(int)n.getNumChildren(); i++ ){
            children.push_back( getValueFor( n[i] ) );
          }
          return NodeManager::currentNM()->mkNode( APPLY_CONSTRUCTOR, children );
        }else{
          const Datatype& dt = ((DatatypeType)(n.getType()).toType()).getDatatype();
          TheoryDatatypes::EqLists* labels = &((TheoryDatatypes*)d_th)->d_labels;
          //otherwise, use which constructor the inst constant is current chosen to be
          if( labels->find( n )!=labels->end() ){
            TheoryDatatypes::EqList* lbl = (*labels->find( n )).second;
            int tIndex = -1;
            if( !lbl->empty() && (*lbl)[ lbl->size()-1 ].getKind()==APPLY_TESTER ){
              Debug("quant-datatypes-debug") << n << " tester is " << (*lbl)[ lbl->size()-1 ] << std::endl;
              tIndex = Datatype::indexOf((*lbl)[ lbl->size()-1 ].getOperator().toExpr());
            }else{
              Debug("quant-datatypes-debug") << "find possible tester choice" << std::endl;
              //must find a possible choice
              vector< bool > possibleCons;
              possibleCons.resize( dt.getNumConstructors(), true );
              for( TheoryDatatypes::EqList::const_iterator j = lbl->begin(); j != lbl->end(); j++ ) {
                Node leqn = (*j);
                possibleCons[ Datatype::indexOf( leqn[0].getOperator().toExpr() ) ] = false;
              }
              for( unsigned int j=0; j<possibleCons.size(); j++ ) {
                if( possibleCons[j] ){
                  tIndex = j;
                  break;
                }
              }
            }
            Assert( tIndex!=-1 );
            Node cons = Node::fromExpr( dt[ tIndex ].getConstructor() );
            Debug("quant-datatypes-debug") << n << " cons is " << cons << std::endl;
            std::vector< Node > children;
            children.push_back( cons );
            for( int i=0; i<(int)dt[ tIndex ].getNumArgs(); i++ ) {
              Node sn = NodeManager::currentNM()->mkNode( APPLY_SELECTOR, Node::fromExpr( dt[tIndex][i].getSelector() ), n );
              if( n.hasAttribute(InstConstantAttribute()) ){
                InstConstantAttribute ica;
                sn.setAttribute(ica,n.getAttribute(InstConstantAttribute()) );
              }
              Node snn = getValueFor( sn );
              children.push_back( snn );
            }
            return NodeManager::currentNM()->mkNode( APPLY_CONSTRUCTOR, children );
          }else{
            return n.getType().mkGroundTerm();
          }
        }
      }
    }
  }
  */
}
