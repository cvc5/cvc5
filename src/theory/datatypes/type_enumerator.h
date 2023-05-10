/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An enumerator for datatypes.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__DATATYPES__TYPE_ENUMERATOR_H
#define CVC5__THEORY__DATATYPES__TYPE_ENUMERATOR_H

#include "expr/dtype.h"
#include "expr/kind.h"
#include "expr/type_node.h"
#include "options/quantifiers_options.h"
#include "theory/type_enumerator.h"

namespace cvc5::internal {
namespace theory {
namespace datatypes {


class DatatypesEnumerator : public TypeEnumeratorBase<DatatypesEnumerator> {
  /** type properties */
  TypeEnumeratorProperties * d_tep;
  /** The datatype we're enumerating */
  const DType& d_datatype;
  /** extra cons */
  unsigned d_has_debruijn;
  /** type */
  TypeNode d_type;
  /** The datatype constructor we're currently enumerating */
  unsigned d_ctor;
  /** The first term to consider in the enumeration */
  Node d_zeroTerm;
  /** Whether we are currently considering the above term */
  bool d_zeroTermActive;
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

  bool hasCyclesDt(const DType& dt)
  {
    return dt.isRecursiveSingleton(d_type)
           || dt.getCardinalityClass(d_type) == CardinalityClass::INFINITE;
  }
  bool hasCycles( TypeNode tn ){
    if( tn.isDatatype() ){
      const DType& dt = tn.getDType();
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
  DatatypesEnumerator(TypeNode type, TypeEnumeratorProperties* tep = nullptr)
      : TypeEnumeratorBase<DatatypesEnumerator>(type),
        d_tep(tep),
        d_datatype(type.getDType()),
        d_type(type),
        d_ctor(0),
        d_zeroTermActive(false)
  {
    d_child_enum = false;
    init();
  }
  DatatypesEnumerator(TypeNode type,
                      bool childEnum,
                      TypeEnumeratorProperties* tep = nullptr)
      : TypeEnumeratorBase<DatatypesEnumerator>(type),
        d_tep(tep),
        d_datatype(type.getDType()),
        d_type(type),
        d_ctor(0),
        d_zeroTermActive(false)
  {
    d_child_enum = childEnum;
    init();
  }
  DatatypesEnumerator(const DatatypesEnumerator& de)
      : TypeEnumeratorBase<DatatypesEnumerator>(de.getType()),
        d_tep(de.d_tep),
        d_datatype(de.d_datatype),
        d_type(de.d_type),
        d_ctor(de.d_ctor),
        d_zeroTerm(de.d_zeroTerm),
        d_zeroTermActive(de.d_zeroTermActive)
  {
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

  Node operator*() override
  {
    Trace("dt-enum-debug") << ": get term " << this << std::endl;
    if (d_zeroTermActive)
    {
      return d_zeroTerm;
    }
    else if (d_ctor < d_has_debruijn + d_datatype.getNumConstructors())
    {
      return getCurrentTerm( d_ctor );
    }
    throw NoMoreValuesException(getType());
  }

  DatatypesEnumerator& operator++() override;

  bool isFinished() override
  {
    return d_ctor >= d_has_debruijn+d_datatype.getNumConstructors();
  }

};/* DatatypesEnumerator */

}  // namespace datatypes
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__DATATYPES__TYPE_ENUMERATOR_H */
