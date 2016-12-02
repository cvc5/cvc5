/*********************                                                        */
/*! \file type_enumerator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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
#include "options/quantifiers_options.h"

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
    return dt.isRecursiveSingleton( d_type.toType() ) || !dt.isFinite( d_type.toType() );
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
        if( prevSize==d_size_limit || ( d_size_limit==0 && d_datatype.isCodatatype() ) || !d_datatype.isInterpretedFinite( d_type.toType() ) ){
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

}/* CVC4::theory::datatypes namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__DATATYPES__TYPE_ENUMERATOR_H */
