/*********************                                                        */
/*! \file first_order_model.cpp
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
 ** \brief Implementation of model engine model class
 **/

#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/rep_set_iterator.h"
#include "theory/quantifiers/model_engine.h"
#include "theory/quantifiers/term_database.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

FirstOrderModel::FirstOrderModel( QuantifiersEngine* qe, context::Context* c, std::string name ) : DefaultModel( c, name, true ),
d_term_db( qe->getTermDatabase() ), d_forall_asserts( c ){

}

void FirstOrderModel::reset(){
  //rebuild models
  d_uf_model_tree.clear();
  d_uf_model_gen.clear();
  d_array_model.clear();
  DefaultModel::reset();
}

void FirstOrderModel::addTerm( Node n ){
  //std::vector< Node > added;
  //d_term_db->addTerm( n, added, false );
  DefaultModel::addTerm( n );
}

void FirstOrderModel::initialize(){
  //this is called after representatives have been chosen and the equality engine has been built
  //for each quantifier, collect all operators we care about
  for( int i=0; i<getNumAssertedQuantifiers(); i++ ){
    Node f = getAssertedQuantifier( i );
    //initialize relevant models within bodies of all quantifiers
    initializeModelForTerm( f[1] );
  }
  //for debugging
  if( Options::current()->printModelEngine ){
    for( std::map< TypeNode, std::vector< Node > >::iterator it = d_rep_set.d_type_reps.begin(); it != d_rep_set.d_type_reps.end(); ++it ){
      if( it->first.isSort() ){
        Message() << "Cardinality( " << it->first << " )" << " = " << it->second.size() << std::endl;
      }
    }
  }
}

void FirstOrderModel::initializeModelForTerm( Node n ){
  if( n.getKind()==APPLY_UF ){
    Node op = n.getOperator();
    if( d_uf_model_tree.find( op )==d_uf_model_tree.end() ){
      TypeNode tn = op.getType();
      tn = tn[ (int)tn.getNumChildren()-1 ];
      //only generate models for predicates and functions with uninterpreted range types
      if( tn==NodeManager::currentNM()->booleanType() || tn.isSort() ){
        d_uf_model_tree[ op ] = uf::UfModelTree( op );
        d_uf_model_gen[ op ].clear();
      }
    }
  }
  /*
  if( n.getType().isArray() ){
    while( n.getKind()==STORE ){
      n = n[0];
    }
    Node nn = getRepresentative( n );
    if( d_array_model.find( nn )==d_array_model.end() ){
      d_array_model[nn] = arrays::ArrayModel( nn, this );
    }
  }
  */
  for( int i=0; i<(int)n.getNumChildren(); i++ ){
    initializeModelForTerm( n[i] );
  }
}

void FirstOrderModel::toStreamFunction( Node n, std::ostream& out ){
  /*
  if( d_uf_model.find( n )!=d_uf_model.end() ){
    //d_uf_model[n].toStream( out );
    Node value = d_uf_model[n].getFunctionValue();
    out << "(" << n << " " << value << ")";
  }else if( d_array_model.find( n )!=d_array_model.end() ){
    Node value = d_array_model[n].getArrayValue();
    out << "(" << n << " " << value << ")" << std::endl;
  }
  */
  DefaultModel::toStreamFunction( n, out );
}

void FirstOrderModel::toStreamType( TypeNode tn, std::ostream& out ){
  DefaultModel::toStreamType( tn, out );
}

Node FirstOrderModel::getInterpretedValue( TNode n ){
  Debug("fo-model") << "get interpreted value " << n << std::endl;
  TypeNode type = n.getType();
  if( type.isFunction() || type.isPredicate() ){
    if( d_uf_models.find( n )==d_uf_models.end() ){
      //use the model tree to generate the model
      Node fn = d_uf_model_tree[n].getFunctionValue();
      d_uf_models[n] = fn;
      return fn;
    }
  /*
  }else if( type.isArray() ){
    if( d_array_model.find( n )!=d_array_model.end() ){
      return d_array_model[n].getArrayValue();
    }else{
      //std::cout << "no array model generated for " << n << std::endl;
    }
  */
  }else if( n.getKind()==APPLY_UF ){
    Node op = n.getOperator();
    if( d_uf_model_tree.find( op )!=d_uf_model_tree.end() ){
      //consult the uf model
      int depIndex;
      return d_uf_model_tree[ op ].getValue( this, n, depIndex );
    }
  }else if( n.getKind()==SELECT ){

  }
  return DefaultModel::getInterpretedValue( n );
}

TermDb* FirstOrderModel::getTermDatabase(){
  return d_term_db;
}


void FirstOrderModel::toStream(std::ostream& out){
  DefaultModel::toStream( out );
#if 0
  out << "---Current Model---" << std::endl;
  out << "Representatives: " << std::endl;
  d_rep_set.toStream( out );
  out << "Functions: " << std::endl;
  for( std::map< Node, uf::UfModel >::iterator it = d_uf_model.begin(); it != d_uf_model.end(); ++it ){
    it->second.toStream( out );
    out << std::endl;
  }
#elif 0
  d_rep_set.toStream( out );
  //print everything not related to UF in equality engine
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    Node rep = getRepresentative( eqc );
    TypeNode type = rep.getType();
    eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &d_equalityEngine );
    while( !eqc_i.isFinished() ){
      //do not print things that have interpretations in model
      if( (*eqc_i).getMetaKind()!=kind::metakind::CONSTANT && !hasInterpretedValue( *eqc_i ) ){
        out << "(" << (*eqc_i) << " " << rep << ")" << std::endl;
      }
      ++eqc_i;
    }
    ++eqcs_i;
  }
  //print functions
  for( std::map< Node, uf::UfModel >::iterator it = d_uf_model.begin(); it != d_uf_model.end(); ++it ){
    it->second.toStream( out );
    out << std::endl;
  }
#endif
}