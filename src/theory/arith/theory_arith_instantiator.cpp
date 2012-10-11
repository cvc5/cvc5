/*********************                                                        */
/*! \file theory_arith_instantiator.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): bobot, mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of instantiator_arith_instantiator class
 **/

#include "theory/arith/theory_arith_instantiator.h"
#include "theory/arith/theory_arith.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers/options.h"
#include "theory/quantifiers/term_database.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;

#define ARITH_INSTANTIATOR_USE_MINUS_DELTA

InstStrategySimplex::InstStrategySimplex( InstantiatorTheoryArith* th, QuantifiersEngine* ie ) :
    InstStrategy( ie ), d_th( th ), d_counter( 0 ){
  d_negOne = NodeManager::currentNM()->mkConst( Rational(-1) );
}

void InstStrategySimplex::processResetInstantiationRound( Theory::Effort effort ){
  d_counter++;
}

int InstStrategySimplex::process( Node f, Theory::Effort effort, int e ){
  if( e<2 ){
    return STATUS_UNFINISHED;
  }else if( e==2 ){
    //Notice() << f << std::endl;
    //Notice() << "Num inst rows = " << d_th->d_instRows[f].size() << std::endl;
    //Notice() << "Num inst constants = " << d_quantEngine->getNumInstantiationConstants( f ) << std::endl;
    Debug("quant-arith-simplex") << "InstStrategySimplex check " << f << ", rows = " << d_th->d_instRows[f].size() << std::endl;
    for( int j=0; j<(int)d_th->d_instRows[f].size(); j++ ){
      ArithVar x = d_th->d_instRows[f][j];
      if( !d_th->d_ceTableaux[x].empty() ){
        Debug("quant-arith-simplex") << "Check row " << x << std::endl;
        //instantiation row will be A*e + B*t = beta,
        // where e is a vector of terms , and t is vector of ground terms.
        // Say one term in A*e is coeff*e_i, where e_i is an instantiation constant
        // We will construct the term ( beta - B*t)/coeff to use for e_i.
        InstMatch m;
        //By default, choose the first instantiation constant to be e_i.
        Node var = d_th->d_ceTableaux[x].begin()->first;
        if( var.getType().isInteger() ){
          std::map< Node, Node >::iterator it = d_th->d_ceTableaux[x].begin();
          //try to find coefficent that is +/- 1
          while( !var.isNull() && !d_th->d_ceTableaux[x][var].isNull() && d_th->d_ceTableaux[x][var]!=d_negOne ){
            ++it;
            if( it==d_th->d_ceTableaux[x].end() ){
              var = Node::null();
            }else{
              var = it->first;
            }
          }
          //otherwise, try one that divides all ground term coefficients? DO_THIS
        }
        if( !var.isNull() ){
          Debug("quant-arith-simplex") << "Instantiate with var " << var << std::endl;
          d_th->doInstantiation( f, d_th->d_tableaux_term[x], x, m, var );
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

InstantiatorTheoryArith::InstantiatorTheoryArith(context::Context* c, QuantifiersEngine* ie, Theory* th) :
Instantiator( c, ie, th ){
  if( options::cbqi() ){
    addInstStrategy( new InstStrategySimplex( this, d_quantEngine ) );
  }
}

void InstantiatorTheoryArith::preRegisterTerm( Node t ){

}

void InstantiatorTheoryArith::assertNode( Node assertion ){
  Debug("quant-arith-assert") << "InstantiatorTheoryArith::check: " << assertion << std::endl;
  d_quantEngine->addTermToDatabase( assertion );
  if( options::cbqi() ){
    if( assertion.hasAttribute(InstConstantAttribute()) ){
      setHasConstraintsFrom( assertion.getAttribute(InstConstantAttribute()) );
    }else if( assertion.getKind()==NOT && assertion[0].hasAttribute(InstConstantAttribute()) ){
      setHasConstraintsFrom( assertion[0].getAttribute(InstConstantAttribute()) );
    }
  }
}

void InstantiatorTheoryArith::processResetInstantiationRound( Theory::Effort effort ){
  if( options::cbqi() ){
    Debug("quant-arith") << "Setting up simplex for instantiator... " << std::endl;
    d_instRows.clear();
    d_tableaux_term.clear();
    d_tableaux.clear();
    d_ceTableaux.clear();
    //search for instantiation rows in simplex tableaux
    ArithVarToNodeMap avtnm = ((TheoryArith*)getTheory())->d_arithvarNodeMap.getArithVarToNodeMap();
    for( ArithVarToNodeMap::iterator it = avtnm.begin(); it != avtnm.end(); ++it ){
      ArithVar x = (*it).first;
      if( ((TheoryArith*)getTheory())->d_partialModel.hasEitherBound( x ) ){
        Node n = (*it).second;
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
          setHasConstraintsFrom( f );
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
  }
}

int InstantiatorTheoryArith::process( Node f, Theory::Effort effort, int e ){
  Debug("quant-arith") << "Arith: Try to solve (" << effort << ") for " << f << "... " << std::endl;
  return InstStrategy::STATUS_UNKNOWN;
}

void InstantiatorTheoryArith::addTermToRow( ArithVar x, Node n, Node& f, NodeBuilder<>& t ){
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

void InstantiatorTheoryArith::debugPrint( const char* c ){
  ArithVarToNodeMap avtnm = ((TheoryArith*)getTheory())->d_arithvarNodeMap.getArithVarToNodeMap();
  for( ArithVarToNodeMap::iterator it = avtnm.begin(); it != avtnm.end(); ++it ){
    ArithVar x = (*it).first;
    Node n = (*it).second;
    //if( ((TheoryArith*)getTheory())->d_partialModel.hasEitherBound( x ) ){
      Debug(c) << x << " : " << n << ", bounds = ";
      if( ((TheoryArith*)getTheory())->d_partialModel.hasLowerBound( x ) ){
        Debug(c) << ((TheoryArith*)getTheory())->d_partialModel.getLowerBound( x );
      }else{
        Debug(c) << "-infty";
      }
      Debug(c) << " <= ";
      Debug(c) << ((TheoryArith*)getTheory())->d_partialModel.getAssignment( x );
      Debug(c) << " <= ";
      if( ((TheoryArith*)getTheory())->d_partialModel.hasUpperBound( x ) ){
        Debug(c) << ((TheoryArith*)getTheory())->d_partialModel.getUpperBound( x );
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
bool InstantiatorTheoryArith::doInstantiation( Node f, Node term, ArithVar x, InstMatch& m, Node var ){
  //first try +delta
  if( doInstantiation2( f, term, x, m, var ) ){
    ++(d_statistics.d_instantiations);
    return true;
  }else{
#ifdef ARITH_INSTANTIATOR_USE_MINUS_DELTA
    //otherwise try -delta
    if( doInstantiation2( f, term, x, m, var, true ) ){
      ++(d_statistics.d_instantiations_minus);
      ++(d_statistics.d_instantiations);
      return true;
    }else{
      return false;
    }
#else
    return false;
#endif
  }
}

bool InstantiatorTheoryArith::doInstantiation2( Node f, Node term, ArithVar x, InstMatch& m, Node var, bool minus_delta ){
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

Node InstantiatorTheoryArith::getTableauxValue( Node n, bool minus_delta ){
  if( ((TheoryArith*)getTheory())->d_arithvarNodeMap.hasArithVar(n) ){
    ArithVar v = ((TheoryArith*)getTheory())->d_arithvarNodeMap.asArithVar( n );
    return getTableauxValue( v, minus_delta );
  }else{
    return NodeManager::currentNM()->mkConst( Rational(0) );
  }
}

Node InstantiatorTheoryArith::getTableauxValue( ArithVar v, bool minus_delta ){
  const Rational& delta = ((TheoryArith*)getTheory())->d_partialModel.getDelta();
  DeltaRational drv = ((TheoryArith*)getTheory())->d_partialModel.getAssignment( v );
  Rational qmodel = drv.substituteDelta( minus_delta ? -delta : delta );
  return mkRationalNode(qmodel);
}

InstantiatorTheoryArith::Statistics::Statistics():
  d_instantiations("InstantiatorTheoryArith::Instantiations_Total", 0),
  d_instantiations_minus("InstantiatorTheoryArith::Instantiations_minus_delta", 0)
{
  StatisticsRegistry::registerStat(&d_instantiations);
  StatisticsRegistry::registerStat(&d_instantiations_minus);
}

InstantiatorTheoryArith::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_instantiations);
  StatisticsRegistry::unregisterStat(&d_instantiations_minus);
}
