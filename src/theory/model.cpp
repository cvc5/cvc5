/*********************                                                        */
/*! \file model.cpp
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
 ** \brief Implementation of model class
 **/

#include "theory/model.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;

void RepSet::clear(){
  d_type_reps.clear();
  d_tmap.clear();
}

void RepSet::add( Node n ){
  TypeNode t = n.getType();
  d_tmap[ n ] = (int)d_type_reps[t].size();
  d_type_reps[t].push_back( n );
}

void RepSet::set( TypeNode t, std::vector< Node >& reps ){
  for( size_t i=0; i<reps.size(); i++ ){
    d_tmap[ reps[i] ] = i;
  }
  d_type_reps[t].insert( d_type_reps[t].begin(), reps.begin(), reps.end() );
}

void RepSet::toStream(std::ostream& out){
#if 0
  for( std::map< TypeNode, std::vector< Node > >::iterator it = d_type_reps.begin(); it != d_type_reps.end(); ++it ){
    out << it->first << " : " << std::endl;
    for( int i=0; i<(int)it->second.size(); i++ ){
      out << "   " << i << ": " << it->second[i] << std::endl;
    }
  }
#else
  for( std::map< TypeNode, std::vector< Node > >::iterator it = d_type_reps.begin(); it != d_type_reps.end(); ++it ){
    if( !it->first.isFunction() && !it->first.isPredicate() ){
      out << "(" << it->first << " " << it->second.size();
      out << " (";
      for( int i=0; i<(int)it->second.size(); i++ ){
        if( i>0 ){ out << " "; }
        out << it->second[i];
      }
      out << ")";
      out << ")" << std::endl;
    }
  }
#endif
}

TheoryModel::TheoryModel( context::Context* c, std::string name ) :
d_equalityEngine( c, name ){
  d_true = NodeManager::currentNM()->mkConst( true );
  d_false = NodeManager::currentNM()->mkConst( false );
}

void TheoryModel::addDefineFunction( Node n ){
  d_define_funcs.push_back( n );
  d_defines.push_back( 0 );
}

void TheoryModel::addDefineType( TypeNode tn ){
  d_define_types.push_back( tn );
  d_defines.push_back( 1 );
}

void TheoryModel::toStreamFunction( Node n, std::ostream& out ){
  out << "(" << n;
  //out << " : " << n.getType();
  out << " ";
  Node value = getValue( n );
  if( n.getType().isSort() ){
    int index = d_ra.getIndexFor( value );
    if( index!=-1 ){
      out << value.getType() << "_" << index;
    }else{
      out << value;
    }
  }else{
    out << value;
  }
  out << ")" << std::endl;
}

void TheoryModel::toStreamType( TypeNode tn, std::ostream& out ){
  out << "(" << tn;
  if( tn.isSort() ){
    if( d_ra.d_type_reps.find( tn )!=d_ra.d_type_reps.end() ){
      out << " " << d_ra.d_type_reps[tn].size();
      //out << " (";
      //for( size_t i=0; i<d_ra.d_type_reps[tn].size(); i++ ){
      //  if( i>0 ){ out << " "; }
      //  out << d_ra.d_type_reps[tn][i];
      //}
      //out << ")";
    }
  }
  out << ")" << std::endl;
}

void TheoryModel::toStream( std::ostream& out ){
  int funcIndex = 0;
  int typeIndex = 0;
  for( size_t i=0; i<d_defines.size(); i++ ){
    if( d_defines[i]==0 ){
      toStreamFunction( d_define_funcs[funcIndex], out );
      funcIndex++;
    }else if( d_defines[i]==1 ){
      toStreamType( d_define_types[typeIndex], out );
      typeIndex++;
    }
  }
}

Node TheoryModel::getValue( TNode n ){
  Debug("model") << "TheoryModel::getValue " << n << std::endl;

  kind::MetaKind metakind = n.getMetaKind();

  //// special case: prop engine handles boolean vars
  //if(metakind == kind::metakind::VARIABLE && n.getType().isBoolean()) {
  //  Debug("model") << "-> Propositional variable." << std::endl;
  //  return d_te->getPropEngine()->getValue( n );
  //}

  // special case: value of a constant == itself
  if(metakind == kind::metakind::CONSTANT) {
    Debug("model") << "-> Constant." << std::endl;
    return n;
  }

  Node nn;
  if( n.getNumChildren()>0 ){
    std::vector< Node > children;
    if( metakind == kind::metakind::PARAMETERIZED ){
      Debug("model-debug") << "get operator: " << n.getOperator() << std::endl;
      children.push_back( n.getOperator() );
    }
    //evaluate the children
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      Node val = getValue( n[i] );
      Debug("model-debug") << i << " : " << n[i] << " -> " << val << std::endl;
      Assert( !val.isNull() );
      children.push_back( val );
    }
    Debug("model-debug") << "Done eval children" << std::endl;
    nn = NodeManager::currentNM()->mkNode( n.getKind(), children );
  }else{
    nn = n;
  }
  //interpretation is the rewritten form
  nn = Rewriter::rewrite( nn );

  // special case: value of a constant == itself
  if(metakind == kind::metakind::CONSTANT) {
    Debug("model") << "-> Theory-interpreted term." << std::endl;
    return nn;
  }else{
    Debug("model") << "-> Model-interpreted term." << std::endl;
    //otherwise, get the interpreted value in the model
    return getInterpretedValue( nn );
  }

  ////case for equality
  //if( n.getKind()==EQUAL ){
  //  Debug("model") << "-> Equality." << std::endl;
  //  Node n1 = getValue( n[0] );
  //  Node n2 = getValue( n[1] );
  //  return NodeManager::currentNM()->mkConst( n1==n2 );
  //}
}

Node TheoryModel::getDomainValue( TypeNode tn, std::vector< Node >& exclude ){
  if( d_ra.d_type_reps.find( tn )!=d_ra.d_type_reps.end() ){
    //try to find a pre-existing arbitrary element
    for( size_t i=0; i<d_ra.d_type_reps[tn].size(); i++ ){
      if( std::find( exclude.begin(), exclude.end(), d_ra.d_type_reps[tn][i] )==exclude.end() ){
        return d_ra.d_type_reps[tn][i];
      }
    }
  }
  return Node::null();
}

//FIXME: use the theory enumerator to generate constants here
Node TheoryModel::getNewDomainValue( TypeNode tn, bool mkConst ){
  if( tn==NodeManager::currentNM()->booleanType() ){
    if( d_ra.d_type_reps[tn].empty() ){
      return d_false;
    }else if( d_ra.d_type_reps[tn].size()==1 ){
      return NodeManager::currentNM()->mkConst( areEqual( d_ra.d_type_reps[tn][0], d_false ) );
    }else{
      return Node::null();
    }
  }else if( tn==NodeManager::currentNM()->integerType() || tn==NodeManager::currentNM()->realType() ){
    int val = 0;
    do{
      Node r = NodeManager::currentNM()->mkConst( Rational(val) );
      if( std::find( d_ra.d_type_reps[tn].begin(), d_ra.d_type_reps[tn].end(), r )==d_ra.d_type_reps[tn].end() &&
          !d_equalityEngine.hasTerm( r ) ){
        return r;
      }
      val++;
    }while( true );
  }else{
    //otherwise must make a variable  FIXME: how to make constants for other sorts?
    //return NodeManager::currentNM()->mkVar( tn );
    return Node::null();
  }
}

/** assert equality */
void TheoryModel::assertEquality( Node a, Node b, bool polarity ){
  d_equalityEngine.assertEquality( a.eqNode(b), polarity, Node::null() );
}

/** assert predicate */
void TheoryModel::assertPredicate( Node a, bool polarity ){
  if( a.getKind()==EQUAL ){
    d_equalityEngine.assertEquality( a, polarity, Node::null() );
  }else{
    d_equalityEngine.assertPredicate( a, polarity, Node::null() );
  }
}

/** assert equality engine */
void TheoryModel::assertEqualityEngine( eq::EqualityEngine* ee ){
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( ee );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    bool predicate = false;
    bool predPolarity = false;
    if( eqc.getType()==NodeManager::currentNM()->booleanType() ){
      predicate = true;
      predPolarity = ee->areEqual( eqc, d_true );
      //FIXME: do we guarentee that all boolean equivalence classes contain either d_true or d_false?
    }
    eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, ee );
    while( !eqc_i.isFinished() ){
      if( predicate ){
        assertPredicate( *eqc_i, predPolarity );
      }else{
        assertEquality( *eqc_i, eqc, true );
      }
      ++eqc_i;
    }
    ++eqcs_i;
  }
}

bool TheoryModel::hasTerm( Node a ){
  return d_equalityEngine.hasTerm( a );
}

Node TheoryModel::getRepresentative( Node a ){
  if( d_equalityEngine.hasTerm( a ) ){
    return d_reps[ d_equalityEngine.getRepresentative( a ) ];
  }else{
    return a;
  }
}

bool TheoryModel::areEqual( Node a, Node b ){
  if( a==b ){
    return true;
  }else if( d_equalityEngine.hasTerm( a ) && d_equalityEngine.hasTerm( b ) ){
    return d_equalityEngine.areEqual( a, b );
  }else{
    return false;
  }
}

bool TheoryModel::areDisequal( Node a, Node b ){
  if( d_equalityEngine.hasTerm( a ) && d_equalityEngine.hasTerm( b ) ){
    return d_equalityEngine.areDisequal( a, b, false );
  }else{
    return false;
  }
}

//for debugging
void TheoryModel::printRepresentativeDebug( const char* c, Node r ){
  if( r.isNull() ){
    Debug( c ) << "null";
  }else if( r.getType()==NodeManager::currentNM()->booleanType() ){
    if( areEqual( r, d_true ) ){
      Debug( c ) << "true";
    }else{
      Debug( c ) << "false";
    }
  }else{
    Debug( c ) << getRepresentative( r );
  }
}

void TheoryModel::printRepresentative( std::ostream& out, Node r ){
  Assert( !r.isNull() );
  if( r.isNull() ){
    out << "null";
  }else if( r.getType()==NodeManager::currentNM()->booleanType() ){
    if( areEqual( r, d_true ) ){
      out  << "true";
    }else{
      out  << "false";
    }
  }else{
    out << getRepresentative( r );
  }
}

DefaultModel::DefaultModel( context::Context* c, std::string name ) : TheoryModel( c, name ){

}

Node DefaultModel::getInterpretedValue( TNode n ){
  TypeNode type = n.getType();
  if( type.isFunction() || type.isPredicate() ){
    //DO_THIS?
    return n;
  }else{
    //first, see if the representative is defined
    if( d_equalityEngine.hasTerm( n ) ){
      n = d_equalityEngine.getRepresentative( n );
      //this check is required since d_equalityEngine.hasTerm( n )
      // does not ensure that n is in an equivalence class in d_equalityEngine
      if( d_reps.find( n )!=d_reps.end() ){
        return d_reps[n];
      }
    }
    //second, try to choose an existing term as value
    std::vector< Node > v_emp;
    Node n2 = getDomainValue( type, v_emp );
    if( !n2.isNull() ){
      return n2;
    }else{
      //otherwise, choose new value
      n2 = getNewDomainValue( type, true );
      if( !n2.isNull() ){
        return n2;
      }else{
        //otherwise, just return itself
        return n;
      }
    }
  }
}

TheoryEngineModelBuilder::TheoryEngineModelBuilder( TheoryEngine* te ) : d_te( te ){

}

void TheoryEngineModelBuilder::buildModel( Model* m ){
  TheoryModel* tm = (TheoryModel*)m;
  //reset representative information
  tm->d_reps.clear();
  tm->d_ra.clear();
  Debug( "model-builder" ) << "TheoryEngineModelBuilder: Collect model info..." << std::endl;
  //collect model info from the theory engine
  d_te->collectModelInfo( tm );
  Debug( "model-builder" ) << "TheoryEngineModelBuilder: Build representatives..." << std::endl;
  //populate term database, store representatives
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &tm->d_equalityEngine );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    //add terms to model
    eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &tm->d_equalityEngine );
    while( !eqc_i.isFinished() ){
      tm->addTerm( *eqc_i );
      ++eqc_i;
    }
    //choose representative for this equivalence class
    Node rep = chooseRepresentative( tm, eqc );
    //store representative in representative set
    if( !rep.isNull() ){
      tm->d_reps[ eqc ] = rep;
      tm->d_ra.add( rep );
    }
    ++eqcs_i;
  }
  //do model-builder specific initialization
  // this should include choosing representatives for equivalence classes that have not yet been
  // assigned representatives
  processBuildModel( tm );
}

Node TheoryEngineModelBuilder::chooseRepresentative( TheoryModel* tm, Node eqc ){
  eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &tm->d_equalityEngine );
  while( !eqc_i.isFinished() ){
    //if constant, use this as representative
    if( (*eqc_i).getMetaKind()==kind::metakind::CONSTANT ){
      return *eqc_i;
    }
    ++eqc_i;
  }
  return Node::null();
}

void TheoryEngineModelBuilder::processBuildModel( TheoryModel* tm ){
  Debug( "model-builder" ) << "TheoryEngineModelBuilder: Complete model..." << std::endl;
  //create constants for all unresolved equivalence classes
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &tm->d_equalityEngine );
  while( !eqcs_i.isFinished() ){
    Node n = *eqcs_i;
    if( tm->d_reps.find( n )!=tm->d_reps.end() ){
      TypeNode tn = n.getType();
      //add new constant to equivalence class
      Node rep = tm->getNewDomainValue( tn, true );
      if( !rep.isNull() ){
        tm->assertEquality( n, rep, true );
      }else{
        rep = n;
      }
      tm->d_reps[ n ] = rep;
      tm->d_ra.add( rep );
    }
    ++eqcs_i;
  }
}
