/*********************                                                        */
/*! \file type_enumerator.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief An enumerator for bitvectors
 **
 ** An enumerator for bitvectors.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__DATATYPES__TYPE_ENUMERATOR_H
#define __CVC4__THEORY__DATATYPES__TYPE_ENUMERATOR_H

#include "theory/type_enumerator.h"
#include "expr/type_node.h"
#include "expr/type.h"
#include "expr/kind.h"

namespace CVC4 {
namespace theory {
namespace datatypes {


class DatatypesEnumerator : public TypeEnumeratorBase<DatatypesEnumerator> {
  /** The datatype we're enumerating */
  const Datatype& d_datatype;
  /** type */
  TypeNode d_type;
  /** The datatype constructor we're currently enumerating */
  unsigned d_ctor;
  /** The "first" constructor to consider; it's non-recursive */
  unsigned d_zeroCtor;
  /** list of type enumerators (one for each type in a selector argument) */
  std::map< TypeNode, unsigned > d_te_index;
  std::vector< TypeEnumerator > d_children;
  /** terms produced for types */
  std::map< TypeNode, std::vector< Node > > d_terms;
  /** arg type of each selector, for each constructor */
  std::vector< std::vector< TypeNode > > d_sel_types;
  /** current index for each argument, for each constructor */
  std::vector< std::vector< unsigned > > d_sel_index;
  /** current sum of argument indicies for each constructor */
  std::vector< int > d_sel_sum;
  /** current bound on the number of times we can iterate argument enumerators */
  unsigned d_size_limit;

  Node getTermEnum( TypeNode tn, unsigned i ){
    if( i<d_terms[tn].size() ){
      return d_terms[tn][i];
    }else{
      Debug("dt-enum-debug") << "get term enum " << tn << " " << i << std::endl;
      std::map< TypeNode, unsigned >::iterator it = d_te_index.find( tn );
      unsigned tei;
      if( it==d_te_index.end() ){
        //initialize child enumerator for type
        tei = d_children.size();
        d_te_index[tn] = tei;
        d_children.push_back( TypeEnumerator( tn ) );
        d_terms[tn].push_back( *d_children[tei] );
      }else{
        tei = it->second;
      }
      //enumerate terms until index is reached
      while( i>=d_terms[tn].size() ){
        ++d_children[tei];
        if( d_children[tei].isFinished() ){
          Debug("dt-enum-debug") << "...fail term enum " << tn << " " << i << std::endl;
          return Node::null();
        }
        d_terms[tn].push_back( *d_children[tei] );
      }
      Debug("dt-enum-debug") << "...return term enum " << tn << " " << i << " : " << d_terms[tn][i] << std::endl;
      return d_terms[tn][i];
    }
  }

  bool increment( unsigned index ){
    Debug("dt-enum") << "Incrementing " << d_type << " " << d_ctor << " at size " << d_sel_sum[index] << "/" << d_size_limit << std::endl;
    if( d_sel_sum[index]==-1 ){
      //first time
      d_sel_sum[index] = 0;
      //special case: no children to iterate
      if( d_sel_types[index].size()==0 ){
        Debug("dt-enum") << "...success (nc) = " << (d_size_limit==0) << std::endl;
        return d_size_limit==0;
      }else{
        Debug("dt-enum") << "...success" << std::endl;
        return true;
      }
    }else{
      unsigned i = 0;
      while( i < d_sel_index[index].size() ){
        //increment if the sum of iterations on arguments is less than the limit
        if( d_sel_sum[index]<(int)d_size_limit ){
          //also check if child enumerator has enough terms
          if( !getTermEnum( d_sel_types[index][i], d_sel_index[index][i]+1 ).isNull() ){
            Debug("dt-enum") << "...success increment child " << i << std::endl;
            d_sel_index[index][i]++;
            d_sel_sum[index]++;
            return true;
          }
        }
        Debug("dt-enum") << "......failed increment child " << i << std::endl;
        //reset child, iterate next
        d_sel_sum[index] -= d_sel_index[index][i];
        d_sel_index[index][i] = 0;
        i++;
      }
      Debug("dt-enum") << "...failure." << std::endl;
      return false;
    }
  }

  Node getCurrentTerm( unsigned index ){
    Debug("dt-enum-debug") << "Get current term at " << index << " " << d_type << "..." << std::endl;
    DatatypeConstructor ctor = d_datatype[index];
    Debug("dt-enum-debug") << "Check last term..." << std::endl;
    //we first check if the last argument (which is forced to make sum of iterated arguments equal to d_size_limit) is defined
    Node lc;
    if( ctor.getNumArgs()>0 ){
      lc = getTermEnum( d_sel_types[index][ctor.getNumArgs()-1], d_size_limit - d_sel_sum[index] );
      if( lc.isNull() ){
        Debug("dt-enum-debug") << "Current infeasible." << std::endl;
        return Node::null();
      }
    }
    Debug("dt-enum-debug") << "Get constructor..." << std::endl;
    NodeBuilder<> b(kind::APPLY_CONSTRUCTOR);
    Type typ;
    if( d_datatype.isParametric() ){
      typ = ctor.getSpecializedConstructorType(d_type.toType());
      b << NodeManager::currentNM()->mkNode(kind::APPLY_TYPE_ASCRIPTION,
                                            NodeManager::currentNM()->mkConst(AscriptionType(typ)), Node::fromExpr( ctor.getConstructor() ) );
    }else{
      b << ctor.getConstructor();
    }
    Debug("dt-enum-debug") << "Get arguments..." << std::endl;
    if( ctor.getNumArgs()>0 ){
      Assert( index<d_sel_types.size() );
      Assert( index<d_sel_index.size() );
      Assert( d_sel_types[index].size()==ctor.getNumArgs() );
      Assert( d_sel_index[index].size()==ctor.getNumArgs()-1 );
      for( int i=0; i<(int)(ctor.getNumArgs()-1); i++ ){
        Node c = getTermEnum( d_sel_types[index][i], d_sel_index[index][i] );
        Assert( !c.isNull() );
        b << c;
      }
      b << lc;
    }
    Node nnn = Node(b);
    Debug("dt-enum-debug") << "Return... " <<  nnn  << std::endl;
    return nnn;
  }

public:

  DatatypesEnumerator(TypeNode type) throw() :
    TypeEnumeratorBase<DatatypesEnumerator>(type),
    d_datatype(DatatypeType(type.toType()).getDatatype()),
    d_type(type),
    d_ctor(0),
    d_zeroCtor(0) {

    //Assert(type.isDatatype());
    Debug("te") << "datatype is datatype? " << type.isDatatype() << std::endl;
    Debug("te") << "datatype is kind " << type.getKind() << std::endl;
    Debug("te") << "datatype is " << type << std::endl;

    /* find the "zero" constructor via mkGroundTerm */
    Node t = type.mkGroundTerm();
    Assert( t.getKind()==kind::APPLY_CONSTRUCTOR );
    d_zeroCtor = Datatype::indexOf( t.getOperator().toExpr() );
    /* start with the constructor for which a ground term is constructed */
    d_ctor = d_zeroCtor;

    for( unsigned i=0; i<d_datatype.getNumConstructors(); ++i ){
      d_sel_types.push_back( std::vector< TypeNode >() );
      d_sel_index.push_back( std::vector< unsigned >() );
      d_sel_sum.push_back( -1 );
      DatatypeConstructor ctor = d_datatype[i];
      Type typ;
      if( d_datatype.isParametric() ){
        typ = ctor.getSpecializedConstructorType(d_type.toType());
      }
      for( unsigned a = 0; a < ctor.getNumArgs(); ++a ){
        TypeNode tn;
        if( d_datatype.isParametric() ){
          tn = TypeNode::fromType( typ )[a];
        }else{
          tn = Node::fromExpr(ctor[a].getSelector()).getType()[1];
        }
        d_sel_types[i].push_back( tn );
        d_sel_index[i].push_back( 0 );
      }
      if( !d_sel_index[i].empty() ){
        d_sel_index[i].pop_back();
      }
    }
    d_size_limit = 0;
    //set up initial conditions (should always succeed)
    bool init_inc = increment( d_ctor );
    AlwaysAssert( init_inc );
  }

  DatatypesEnumerator(const DatatypesEnumerator& de) throw() :
    TypeEnumeratorBase<DatatypesEnumerator>(de.getType()),
    d_datatype(de.d_datatype),
    d_type(de.d_type),
    d_ctor(de.d_ctor),
    d_zeroCtor(de.d_zeroCtor) {

    for( std::map< TypeNode, unsigned >::const_iterator it = de.d_te_index.begin(); it != de.d_te_index.end(); ++it ){
      d_te_index[it->first] = it->second;
    }
    for( std::map< TypeNode, std::vector< Node > >::const_iterator it = de.d_terms.begin(); it != de.d_terms.end(); ++it ){
      d_terms[it->first].insert( d_terms[it->first].end(), it->second.begin(), it->second.end() );
    }
    for( unsigned i=0; i<de.d_sel_types.size(); i++ ){
      d_sel_types.push_back( std::vector< TypeNode >() );
      d_sel_types[i].insert( d_sel_types[i].end(), de.d_sel_types[i].begin(), de.d_sel_types[i].end() );
    }
    for( unsigned i=0; i<de.d_sel_index.size(); i++ ){
      d_sel_index.push_back( std::vector< unsigned >() );
      d_sel_index[i].insert( d_sel_index[i].end(), de.d_sel_index[i].begin(), de.d_sel_index[i].end() );
    }

    d_children.insert( d_children.end(), de.d_children.begin(), de.d_children.end() );
    d_sel_sum.insert( d_sel_sum.end(), de.d_sel_sum.begin(), de.d_sel_sum.end() );
    d_size_limit = de.d_size_limit;
  }

  ~DatatypesEnumerator() throw() {
  }

  Node operator*() throw(NoMoreValuesException) {
    Debug("dt-enum-debug") << ": get term " << this << std::endl;
    if(d_ctor < d_datatype.getNumConstructors()) {
      return getCurrentTerm( d_ctor );
    } else {
      throw NoMoreValuesException(getType());
    }
  }

  DatatypesEnumerator& operator++() throw() {
    Debug("dt-enum-debug") << ": increment " << this << std::endl;
    unsigned prevSize = d_size_limit;
    while(d_ctor < d_datatype.getNumConstructors()) {
      //increment at index
      while( increment( d_ctor ) ){
        Node n = getCurrentTerm( d_ctor );
        if( !n.isNull() ){
          return *this;
        }
      }
      // Here, we need to step from the current constructor to the next one

      // Find the next constructor (only complicated by the notion of the "zero" constructor
      d_ctor = (d_ctor == d_zeroCtor) ? 0 : d_ctor + 1;
      if(d_ctor == d_zeroCtor) {
        ++d_ctor;
      }
      if( d_ctor>=d_datatype.getNumConstructors() ){
        //try next size limit as long as new terms were generated at last size
        if( prevSize==d_size_limit ){
          d_size_limit++;
          d_ctor = d_zeroCtor;
          for( unsigned i=0; i<d_sel_sum.size(); i++ ){
            d_sel_sum[i] = -1;
          }
        }
      }
    }
    return *this;
  }

  bool isFinished() throw() {
    return d_ctor >= d_datatype.getNumConstructors();
  }

};/* DatatypesEnumerator */

class TupleEnumerator : public TypeEnumeratorBase<TupleEnumerator> {
  TypeEnumerator** d_enumerators;

  /** Allocate and initialize the delegate enumerators */
  void newEnumerators() {
    d_enumerators = new TypeEnumerator*[getType().getNumChildren()];
    for(size_t i = 0; i < getType().getNumChildren(); ++i) {
      d_enumerators[i] = new TypeEnumerator(getType()[i]);
    }
  }

  void deleteEnumerators() throw() {
    if(d_enumerators != NULL) {
      for(size_t i = 0; i < getType().getNumChildren(); ++i) {
        delete d_enumerators[i];
      }
      delete [] d_enumerators;
      d_enumerators = NULL;
    }
  }

public:

  TupleEnumerator(TypeNode type) throw() :
    TypeEnumeratorBase<TupleEnumerator>(type) {
    Assert(type.isTuple());
    newEnumerators();
  }

  TupleEnumerator(const TupleEnumerator& te) throw() :
    TypeEnumeratorBase<TupleEnumerator>(te.getType()),
    d_enumerators(NULL) {

    if(te.d_enumerators != NULL) {
      newEnumerators();
      for(size_t i = 0; i < getType().getNumChildren(); ++i) {
        *d_enumerators[i] = TypeEnumerator(*te.d_enumerators[i]);
      }
    }
  }

  ~TupleEnumerator() throw() {
    deleteEnumerators();
  }

  Node operator*() throw(NoMoreValuesException) {
    if(isFinished()) {
      throw NoMoreValuesException(getType());
    }

    NodeBuilder<> nb(kind::TUPLE);
    for(size_t i = 0; i < getType().getNumChildren(); ++i) {
      nb << **d_enumerators[i];
    }
    return Node(nb);
  }

  TupleEnumerator& operator++() throw() {
    if(isFinished()) {
      return *this;
    }

    size_t i;
    for(i = 0; i < getType().getNumChildren(); ++i) {
      if(d_enumerators[i]->isFinished()) {
        *d_enumerators[i] = TypeEnumerator(getType()[i]);
      } else {
        ++*d_enumerators[i];
        return *this;
      }
    }

    deleteEnumerators();

    return *this;
  }

  bool isFinished() throw() {
    return d_enumerators == NULL;
  }

};/* TupleEnumerator */

class RecordEnumerator : public TypeEnumeratorBase<RecordEnumerator> {
  TypeEnumerator** d_enumerators;

  /** Allocate and initialize the delegate enumerators */
  void newEnumerators() {
    const Record& rec = getType().getConst<Record>();
    d_enumerators = new TypeEnumerator*[rec.getNumFields()];
    for(size_t i = 0; i < rec.getNumFields(); ++i) {
      d_enumerators[i] = new TypeEnumerator(TypeNode::fromType(rec[i].second));
    }
  }

  void deleteEnumerators() throw() {
    if(d_enumerators != NULL) {
      const Record& rec = getType().getConst<Record>();
      for(size_t i = 0; i < rec.getNumFields(); ++i) {
        delete d_enumerators[i];
      }
      delete [] d_enumerators;
      d_enumerators = NULL;
    }
  }

public:

  RecordEnumerator(TypeNode type) throw() :
    TypeEnumeratorBase<RecordEnumerator>(type) {
    Assert(type.isRecord());
    newEnumerators();
  }

  RecordEnumerator(const RecordEnumerator& re) throw() :
    TypeEnumeratorBase<RecordEnumerator>(re.getType()),
    d_enumerators(NULL) {

    if(re.d_enumerators != NULL) {
      newEnumerators();
      for(size_t i = 0; i < getType().getNumChildren(); ++i) {
        *d_enumerators[i] = TypeEnumerator(*re.d_enumerators[i]);
      }
    }
  }

  ~RecordEnumerator() throw() {
    deleteEnumerators();
  }

  Node operator*() throw(NoMoreValuesException) {
    if(isFinished()) {
      throw NoMoreValuesException(getType());
    }

    NodeBuilder<> nb(kind::RECORD);
    Debug("te") << "record enumerator: creating record of type " << getType() << std::endl;
    nb << getType();
    const Record& rec = getType().getConst<Record>();
    for(size_t i = 0; i < rec.getNumFields(); ++i) {
      Debug("te") << " - " << i << " " << std::flush << "=> " << **d_enumerators[i] << std::endl;
      nb << **d_enumerators[i];
    }
    return Node(nb);
  }

  RecordEnumerator& operator++() throw() {
    if(isFinished()) {
      return *this;
    }

    size_t i;
    const Record& rec = getType().getConst<Record>();
    for(i = 0; i < rec.getNumFields(); ++i) {
      if(d_enumerators[i]->isFinished()) {
        *d_enumerators[i] = TypeEnumerator(TypeNode::fromType(rec[i].second));
      } else {
        ++*d_enumerators[i];
        return *this;
      }
    }

    deleteEnumerators();

    return *this;
  }

  bool isFinished() throw() {
    return d_enumerators == NULL;
  }

};/* RecordEnumerator */

}/* CVC4::theory::datatypes namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__DATATYPES__TYPE_ENUMERATOR_H */
