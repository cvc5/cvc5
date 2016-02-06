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
 ** \brief An enumerator for datatypes
 **
 ** An enumerator for datatypes.
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
  /** type properties */
  TypeEnumeratorProperties * d_tep;
  /** The datatype we're enumerating */
  const Datatype& d_datatype;
  /** extra cons */
  unsigned d_has_debruijn;
  /** type */
  TypeNode d_type;
  /** The datatype constructor we're currently enumerating */
  unsigned d_ctor;
  /** The "first" constructor to consider; it's non-recursive */
  unsigned d_zeroCtor;
  /** list of type enumerators (one for each type in a selector argument) */
  std::map< TypeNode, unsigned > d_te_index;
  std::vector< TypeEnumerator > d_children;
  //std::vector< DatatypesEnumerator > d_dt_children;
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
  /** child */
  bool d_child_enum;

  bool hasCyclesDt( const Datatype& dt ) {
    return dt.isRecursiveSingleton() || !dt.isFinite();
  }
  bool hasCycles( TypeNode tn ){
    if( tn.isDatatype() ){
      const Datatype& dt = ((DatatypeType)(tn).toType()).getDatatype();
      return hasCyclesDt( dt );
    }else{
      return false;
    }
  }

  Node getTermEnum( TypeNode tn, unsigned i );

  bool increment( unsigned index );

  Node getCurrentTerm( unsigned index );

  void init();
public:

  DatatypesEnumerator(TypeNode type, TypeEnumeratorProperties * tep = NULL) throw() :
    TypeEnumeratorBase<DatatypesEnumerator>(type),
    d_tep(tep),
    d_datatype(DatatypeType(type.toType()).getDatatype()),
    d_type(type) {
    d_child_enum = false;
    init();
  }
  DatatypesEnumerator(TypeNode type, bool childEnum, TypeEnumeratorProperties * tep = NULL) throw() :
    TypeEnumeratorBase<DatatypesEnumerator>(type),
    d_tep(tep),
    d_datatype(DatatypeType(type.toType()).getDatatype()),
    d_type(type) {
    d_child_enum = childEnum;
    init();
  }
  DatatypesEnumerator(const DatatypesEnumerator& de) throw() :
    TypeEnumeratorBase<DatatypesEnumerator>(de.getType()),
    d_tep(de.d_tep),
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
    d_has_debruijn = de.d_has_debruijn;
    d_child_enum = de.d_child_enum;
  }

  virtual ~DatatypesEnumerator() throw() {
  }

  Node operator*() throw(NoMoreValuesException) {
    Debug("dt-enum-debug") << ": get term " << this << std::endl;
    if(d_ctor < d_has_debruijn + d_datatype.getNumConstructors()) {
      return getCurrentTerm( d_ctor );
    } else {
      throw NoMoreValuesException(getType());
    }
  }

  DatatypesEnumerator& operator++() throw() {
    Debug("dt-enum-debug") << ": increment " << this << std::endl;
    unsigned prevSize = d_size_limit;
    while(d_ctor < d_has_debruijn+d_datatype.getNumConstructors()) {
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
      if( d_ctor>=d_has_debruijn+d_datatype.getNumConstructors() ){
        //try next size limit as long as new terms were generated at last size, or other cases
        if( prevSize==d_size_limit || ( d_size_limit==0 && d_datatype.isCodatatype() ) || !d_datatype.isFinite() ){
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
    return d_ctor >= d_has_debruijn+d_datatype.getNumConstructors();
  }

};/* DatatypesEnumerator */

class TupleEnumerator : public TypeEnumeratorBase<TupleEnumerator> {
  TypeEnumeratorProperties * d_tep;
  TypeEnumerator** d_enumerators;

  /** Allocate and initialize the delegate enumerators */
  void newEnumerators() {
    d_enumerators = new TypeEnumerator*[getType().getNumChildren()];
    for(size_t i = 0; i < getType().getNumChildren(); ++i) {
      d_enumerators[i] = new TypeEnumerator(getType()[i], d_tep);
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

  TupleEnumerator(TypeNode type, TypeEnumeratorProperties * tep = NULL) throw() :
    TypeEnumeratorBase<TupleEnumerator>(type), d_tep(tep) {
    Assert(type.isTuple());
    newEnumerators();
  }

  TupleEnumerator(const TupleEnumerator& te) throw() :
    TypeEnumeratorBase<TupleEnumerator>(te.getType()),
    d_tep(te.d_tep),
    d_enumerators(NULL) {

    if(te.d_enumerators != NULL) {
      newEnumerators();
      for(size_t i = 0; i < getType().getNumChildren(); ++i) {
        *d_enumerators[i] = TypeEnumerator(*te.d_enumerators[i]);
      }
    }
  }

  virtual ~TupleEnumerator() throw() {
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
        *d_enumerators[i] = TypeEnumerator(getType()[i], d_tep);
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
  TypeEnumeratorProperties * d_tep;
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

  RecordEnumerator(TypeNode type, TypeEnumeratorProperties * tep = NULL) throw() :
    TypeEnumeratorBase<RecordEnumerator>(type), d_tep(tep) {
    Assert(type.isRecord());
    newEnumerators();
  }

  RecordEnumerator(const RecordEnumerator& re) throw() :
    TypeEnumeratorBase<RecordEnumerator>(re.getType()),
    d_tep(re.d_tep),
    d_enumerators(NULL) {

    if(re.d_enumerators != NULL) {
      newEnumerators();
      for(size_t i = 0; i < getType().getNumChildren(); ++i) {
        *d_enumerators[i] = TypeEnumerator(*re.d_enumerators[i]);
      }
    }
  }

  virtual ~RecordEnumerator() throw() {
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
