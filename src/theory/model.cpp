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
#include "util/datatype.h"
#include "theory/uf/theory_uf_model.h"

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

void TheoryModel::reset(){
  d_reps.clear();
  d_rep_set.clear();
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
  out << " : " << n.getType();
  out << " ";
  Node value = getValue( n );
  /*
  if( n.getType().isSort() ){
    int index = d_rep_set.getIndexFor( value );
    if( index!=-1 ){
      out << value.getType() << "_" << index;
    }else{
      out << value;
    }
  }else{
  */
  out << value;
  out << ")" << std::endl;
}

void TheoryModel::toStreamType( TypeNode tn, std::ostream& out ){
  out << "(" << tn;
  if( tn.isSort() ){
    if( d_rep_set.d_type_reps.find( tn )!=d_rep_set.d_type_reps.end() ){
      out << " " << d_rep_set.d_type_reps[tn].size();
      //out << " (";
      //for( size_t i=0; i<d_rep_set.d_type_reps[tn].size(); i++ ){
      //  if( i>0 ){ out << " "; }
      //  out << d_rep_set.d_type_reps[tn][i];
      //}
      //out << ")";
    }
  }
  out << ")" << std::endl;
}

void TheoryModel::toStream( std::ostream& out ){
  /*//for debugging
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &d_equalityEngine );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    Debug("get-model-debug") << eqc << " : " << eqc.getType() << " : " << std::endl;
    out << "   ";
    //add terms to model
    eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &d_equalityEngine );
    while( !eqc_i.isFinished() ){
      out << (*eqc_i) << " ";
      ++eqc_i;
    }
    out << std::endl;
    ++eqcs_i;
  }
  */
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

  //// special case: prop engine handles boolean vars
  //if(n.isVar() && n.getType().isBoolean()) {
  //  Debug("model") << "-> Propositional variable." << std::endl;
  //  return d_te->getPropEngine()->getValue( n );
  //}

  // special case: value of a constant == itself
  if(n.isConst()) {
    Debug("model") << "-> Constant." << std::endl;
    return n;
  }

  Node nn;
  if( n.getNumChildren()>0 ){
    std::vector< Node > children;
    if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
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
  if(n.isConst()) {
    Debug("model") << "-> Theory-interpreted term." << std::endl;
    return nn;
  }else{
    Debug("model") << "-> Model-interpreted term." << std::endl;
    //otherwise, get the interpreted value in the model
    return getInterpretedValue( nn );
  }
}

Node TheoryModel::getDomainValue( TypeNode tn, std::vector< Node >& exclude ){
  if( d_rep_set.d_type_reps.find( tn )!=d_rep_set.d_type_reps.end() ){
    //try to find a pre-existing arbitrary element
    for( size_t i=0; i<d_rep_set.d_type_reps[tn].size(); i++ ){
      if( std::find( exclude.begin(), exclude.end(), d_rep_set.d_type_reps[tn][i] )==exclude.end() ){
        return d_rep_set.d_type_reps[tn][i];
      }
    }
  }
  return Node::null();
}

//FIXME: use the theory enumerator to generate constants here
Node TheoryModel::getNewDomainValue( TypeNode tn ){
  if( tn==NodeManager::currentNM()->booleanType() ){
    if( d_rep_set.d_type_reps[tn].empty() ){
      return d_false;
    }else if( d_rep_set.d_type_reps[tn].size()==1 ){
      return NodeManager::currentNM()->mkConst( areEqual( d_rep_set.d_type_reps[tn][0], d_false ) );
    }else{
      return Node::null();
    }
  }else if( tn==NodeManager::currentNM()->integerType() || tn==NodeManager::currentNM()->realType() ){
    int val = 0;
    do{
      Node r = NodeManager::currentNM()->mkConst( Rational(val) );
      if( std::find( d_rep_set.d_type_reps[tn].begin(), d_rep_set.d_type_reps[tn].end(), r )==d_rep_set.d_type_reps[tn].end() &&
          !d_equalityEngine.hasTerm( r ) ){
        return r;
      }
      val++;
    }while( true );
  }else{
    //otherwise must make a variable  FIXME: how to make constants for other sorts?
    //return NodeManager::currentNM()->mkSkolem( tn );
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
void TheoryModel::assertEqualityEngine( const eq::EqualityEngine* ee ){
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
    Node r = d_equalityEngine.getRepresentative( a );
    return d_reps[ r ];
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

DefaultModel::DefaultModel( context::Context* c, std::string name, bool enableFuncModels ) :
TheoryModel( c, name ), d_enableFuncModels( enableFuncModels ){

}

void DefaultModel::addTerm( Node n ){
  //must collect UF terms
  if( d_enableFuncModels && n.getKind()==APPLY_UF ){
    d_uf_terms[ n.getOperator() ].push_back( n );
  }
}

void DefaultModel::reset(){
  d_uf_terms.clear();
  d_uf_models.clear();
  TheoryModel::reset();
}

Node DefaultModel::getInterpretedValue( TNode n ){
  TypeNode type = n.getType();
  if( type.isFunction() || type.isPredicate() ){
    //for function models
    if( d_enableFuncModels ){
      if( d_uf_models.find( n )==d_uf_models.end() ){
        uf::UfModelTree ufmt( n );
        Node default_v;
        for( size_t i=0; i<d_uf_terms[n].size(); i++ ){
          Node un = d_uf_terms[n][i];
          Node v = getRepresentative( un );
          ufmt.setValue( this, un, v );
          default_v = v;
        }
        if( default_v.isNull() ){
          default_v = getInterpretedValue( NodeManager::currentNM()->mkSkolem( type.getRangeType() ) );
        }
        ufmt.setDefaultValue( this, default_v );
        ufmt.simplify();
        d_uf_models[n] = ufmt.getFunctionValue();
      }
      return d_uf_models[n];
    }else{
      return n;
    }
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
      n2 = getNewDomainValue( type );
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
  tm->reset();
  //collect model info from the theory engine
  Debug( "model-builder" ) << "TheoryEngineModelBuilder: Collect model info..." << std::endl;
  d_te->collectModelInfo( tm );
  //unresolved equivalence classes
  std::map< Node, bool > unresolved_eqc;
  std::map< TypeNode, bool > unresolved_types;
  std::map< Node, std::vector< Node > > selects;
  std::map< Node, Node > apply_constructors;
  Debug( "model-builder" ) << "TheoryEngineModelBuilder: Build representatives..." << std::endl;
  //populate term database, store constant representatives
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( &tm->d_equalityEngine );
  while( !eqcs_i.isFinished() ){
    Node eqc = (*eqcs_i);
    TypeNode eqct = eqc.getType();
    //initialize unresolved type information
    initializeType( eqct, unresolved_types );
    //add terms to model, get constant rep if possible
    Node const_rep;
    eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &tm->d_equalityEngine );
    while( !eqc_i.isFinished() ){
      Node n = *eqc_i;
      //check if this is constant, if so, we will use it as representative
      if( n.isConst() ){
        const_rep = n;
      }
      //theory-specific information needed
      if( n.getKind()==SELECT ){
        selects[ n[0] ].push_back( n );
      }else if( n.getKind()==APPLY_CONSTRUCTOR ){
        apply_constructors[ eqc ] = n;
      }
      //model-specific processing of the term, this will include
      tm->addTerm( n );
      ++eqc_i;
    }
    //store representative in representative set
    if( !const_rep.isNull() ){
      //Message() << "Constant rep " << const_rep << " for " << eqc << std::endl;
      tm->d_reps[ eqc ] = const_rep;
      tm->d_rep_set.add( const_rep );
    }else{
      //Message() << "** unresolved eqc " << eqc << std::endl;
      unresolved_eqc[ eqc ] = true;
      unresolved_types[ eqct ] = true;
    }
    ++eqcs_i;
  }
  //choose representatives for unresolved equivalence classes
  Debug( "model-builder" ) << "TheoryEngineModelBuilder: Complete model..." << std::endl;
  bool fixedPoint;
  do{
    fixedPoint = true;
    //for calculating unresolved types
    std::map< TypeNode, bool > unresolved_types_next;
    for( std::map< TypeNode, bool >::iterator it = unresolved_types.begin(); it != unresolved_types.end(); ++it ){
      unresolved_types_next[ it->first ] = false;
    }
    //try to resolve each unresolved equivalence class
    for( std::map< Node, bool >::iterator it = unresolved_eqc.begin(); it != unresolved_eqc.end(); ++it ){
      if( it->second ){
        Node n = it->first;
        TypeNode tn = n.getType();
        Node rep;
        bool mkRep = true;
        if( tn.isArray() ){
          TypeNode index_t = tn.getArrayIndexType();
          TypeNode elem_t = tn.getArrayConstituentType();
          if( !unresolved_types[ index_t ] && !unresolved_types[ elem_t ] ){
            //collect all relevant set values of n
            std::vector< Node > arr_selects;
            std::vector< Node > arr_select_values;
            Node nbase = n;
            while( nbase.getKind()==STORE ){
              arr_selects.push_back( tm->getRepresentative( nbase[1] ) );
              arr_select_values.push_back( tm->getRepresentative( nbase[2] ) );
              nbase = nbase[0];
            }
            eq::EqClassIterator eqc_i = eq::EqClassIterator( n, &tm->d_equalityEngine );
            while( !eqc_i.isFinished() ){
              for( int i=0; i<(int)selects[ *eqc_i ].size(); i++ ){
                Node r = tm->getRepresentative( selects[ *eqc_i ][i][1] );
                if( std::find( arr_selects.begin(), arr_selects.end(), r )==arr_selects.end() ){
                  arr_selects.push_back( r );
                  arr_select_values.push_back( tm->getRepresentative( selects[ *eqc_i ][i] ) );
                }
              }
              ++eqc_i;
            }
            //now, construct based on select/value pairs
            //TODO: make this a constant
            rep = chooseRepresentative( tm, nbase );
            for( int i=0; i<(int)arr_selects.size(); i++ ){
              rep = NodeManager::currentNM()->mkNode( STORE, rep, arr_selects[i], arr_select_values[i] );
            }
          }
          mkRep = false;
        }else if( tn.isDatatype() ){
          if( apply_constructors.find( n )!=apply_constructors.end() ){
            Node ac = apply_constructors[n];
            std::vector< Node > children;
            children.push_back( ac.getOperator() );
            for( size_t i = 0; i<ac.getNumChildren(); i++ ){
              Node acir = ac[i];
              if( tm->d_equalityEngine.hasTerm( acir ) ){
                acir = tm->d_equalityEngine.getRepresentative( acir );
              }
              if( unresolved_eqc.find( acir )==unresolved_eqc.end() ){
                Message() << "TheoryEngineModelBuilder::buildModel : Datatype argument does not exist in the model " << acir << std::endl;
                acir = Node::null();
              }
              if( acir.isNull() || unresolved_eqc[ acir ] ){
                mkRep = false;
                break;
              }else{
                children.push_back( tm->getRepresentative( acir ) );
              }
            }
            if( mkRep ){
              rep = NodeManager::currentNM()->mkNode( APPLY_CONSTRUCTOR, children );
            }
          }else{
            Message() << "TheoryEngineModelBuilder::buildModel : Do not know how to resolve datatype equivalence class " << n << std::endl;
          }
          mkRep = false;
        }
        if( mkRep ){
          rep = chooseRepresentative( tm, n );
        }
        if( !rep.isNull() ){
          tm->assertEquality( n, rep, true );
          tm->d_reps[ n ] = rep;
          tm->d_rep_set.add( rep );
          unresolved_eqc[ n ] = false;
          fixedPoint = false;
        }else{
          unresolved_types_next[ tn ] = true;
        }
      }
    }
    //for calculating unresolved types
    for( std::map< TypeNode, bool >::iterator it = unresolved_types.begin(); it != unresolved_types.end(); ++it ){
      unresolved_types[ it->first ] = unresolved_types_next[ it->first ];
    }
  }while( !fixedPoint );

  //for all unresolved equivalence classes, just get new domain value
  //  this should typically never happen (all equivalence classes should be resolved at this point)
  for( std::map< Node, bool >::iterator it = unresolved_eqc.begin(); it != unresolved_eqc.end(); ++it ){
    if( it->second ){
      Node n = it->first;
      Node rep = chooseRepresentative( tm, n );
      tm->assertEquality( n, rep, true );
      tm->d_reps[ n ] = rep;
      tm->d_rep_set.add( rep );
      //FIXME: Assertion failure here?
      Message() << "Warning : Unresolved eqc, assigning " << rep << " for eqc( " << n << " ), type = " << n.getType() << std::endl;
    }
  }

  //model-specific initialization
  processBuildModel( tm );
}

void TheoryEngineModelBuilder::initializeType( TypeNode tn, std::map< TypeNode, bool >& unresolved_types ){
  if( unresolved_types.find( tn )==unresolved_types.end() ){
    unresolved_types[tn] = false;
    if( tn.isArray() ){
      initializeType( tn.getArrayIndexType(), unresolved_types );
      initializeType( tn.getArrayConstituentType(), unresolved_types );
    }else if( tn.isDatatype() ){
      const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
      for( size_t i = 0; i<dt.getNumConstructors(); i++ ){
        for( size_t j = 0; j<dt[i].getNumArgs(); j++ ){
          initializeType( TypeNode::fromType( dt[i][j].getType() ), unresolved_types );
        }
      }
    }
  }
}

Node TheoryEngineModelBuilder::chooseRepresentative( TheoryModel* m, Node eqc ){
  //try to get a new domain value
  Node rep = m->getNewDomainValue( eqc.getType() );
  if( !rep.isNull() ){
    return rep;
  }else{
    //if we can't get new domain value, just return eqc itself (this typically should not happen)
    //FIXME: Assertion failure here?
    return eqc;
  }
}
