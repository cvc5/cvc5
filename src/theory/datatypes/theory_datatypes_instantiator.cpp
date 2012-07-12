/*********************                                                        */
/*! \file theory_datatypes_instantiator.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of theory_datatypes_instantiator class
 **/

#include "theory/datatypes/theory_datatypes_instantiator.h"
#include "theory/datatypes/theory_datatypes.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers/term_database.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::datatypes;

InstantiatorTheoryDatatypes::InstantiatorTheoryDatatypes(context::Context* c, QuantifiersEngine* ie, Theory* th) :
Instantiator( c, ie, th ){

}

void InstantiatorTheoryDatatypes::assertNode( Node assertion ){
  Debug("quant-datatypes-assert") << "InstantiatorTheoryDatatypes::check: " << assertion << std::endl;
  d_quantEngine->addTermToDatabase( assertion );
  if( Options::current()->cbqi ){
    if( assertion.hasAttribute(InstConstantAttribute()) ){
      setHasConstraintsFrom( assertion.getAttribute(InstConstantAttribute()) );
    }else if( assertion.getKind()==NOT && assertion[0].hasAttribute(InstConstantAttribute()) ){
      setHasConstraintsFrom( assertion[0].getAttribute(InstConstantAttribute()) );
    }
  }
}

void InstantiatorTheoryDatatypes::processResetInstantiationRound( Theory::Effort effort ){

}


int InstantiatorTheoryDatatypes::process( Node f, Theory::Effort effort, int e ){
  Debug("quant-datatypes") << "Datatypes: Try to solve (" << e << ") for " << f << "... " << std::endl;
  if( Options::current()->cbqi ){
    if( e<2 ){
      return InstStrategy::STATUS_UNFINISHED;
    }else if( e==2 ){
      InstMatch m;
      for( int j = 0; j<(int)d_quantEngine->getTermDatabase()->getNumInstantiationConstants( f ); j++ ){
        Node i = d_quantEngine->getTermDatabase()->getInstantiationConstant( f, j );
        if( i.getType().isDatatype() ){
          Node n = getValueFor( i );
          Debug("quant-datatypes-debug") << "Value for " << i << " is " << n << std::endl;
          m.d_map[ i ] = n;
        }
      }
      d_quantEngine->addInstantiation( f, m );
    }
  }
  return InstStrategy::STATUS_UNKNOWN;
}

Node InstantiatorTheoryDatatypes::getValueFor( Node n ){
  //simply get the ground value for n in the current model, if it exists,
  //  or return an arbitrary ground term otherwise
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
}

InstantiatorTheoryDatatypes::Statistics::Statistics():
  d_instantiations("InstantiatorTheoryDatatypes::Instantiations_Total", 0)
{
  StatisticsRegistry::registerStat(&d_instantiations);
}

InstantiatorTheoryDatatypes::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_instantiations);
}

bool InstantiatorTheoryDatatypes::hasTerm( Node a ){
  return ((TheoryDatatypes*)d_th)->hasTerm( a );
}

bool InstantiatorTheoryDatatypes::areEqual( Node a, Node b ){
  return ((TheoryDatatypes*)d_th)->areEqual( a, b );
}

bool InstantiatorTheoryDatatypes::areDisequal( Node a, Node b ){
  return ((TheoryDatatypes*)d_th)->areDisequal( a, b );
}

Node InstantiatorTheoryDatatypes::getRepresentative( Node a ){
  return ((TheoryDatatypes*)d_th)->getRepresentative( a );
}
