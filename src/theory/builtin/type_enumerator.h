/*********************                                                        */
/*! \file type_enumerator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Enumerator for uninterpreted sorts
 **
 ** Enumerator for uninterpreted sorts.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BUILTIN__TYPE_ENUMERATOR_H
#define __CVC4__THEORY__BUILTIN__TYPE_ENUMERATOR_H

#include "expr/kind.h"
#include "expr/type_node.h"
#include "expr/uninterpreted_constant.h"
#include "theory/type_enumerator.h"
#include "theory/builtin/theory_builtin_rewriter.h"
#include "util/integer.h"

namespace CVC4 {
namespace theory {
namespace builtin {

class UninterpretedSortEnumerator : public TypeEnumeratorBase<UninterpretedSortEnumerator> {
  Integer d_count;
  bool d_has_fixed_bound;
  Integer d_fixed_bound;
public:

  UninterpretedSortEnumerator(TypeNode type, TypeEnumeratorProperties * tep = NULL) :
    TypeEnumeratorBase<UninterpretedSortEnumerator>(type),
    d_count(0) {
    Assert(type.getKind() == kind::SORT_TYPE);
    d_has_fixed_bound = false;
    Trace("uf-type-enum") << "UF enum " << type << ", tep = " << tep << std::endl;
    if( tep && tep->d_fixed_usort_card ){
      d_has_fixed_bound = true;
      std::map< TypeNode, Integer >::iterator it = tep->d_fixed_card.find( type );
      if( it!=tep->d_fixed_card.end() ){
        d_fixed_bound = it->second;
      }else{
        d_fixed_bound = Integer(1);
      }
      Trace("uf-type-enum") << "...fixed bound : " << d_fixed_bound << std::endl;
    }
  }

  Node operator*() {
    if(isFinished()) {
      throw NoMoreValuesException(getType());
    }
    return NodeManager::currentNM()->mkConst(UninterpretedConstant(getType().toType(), d_count));
  }

  UninterpretedSortEnumerator& operator++() throw() {
    d_count += 1;
    return *this;
  }

  bool isFinished() throw() {
    if( d_has_fixed_bound ){
      return d_count>=d_fixed_bound;
    }else{
      return false;
    }
  }

};/* class UninterpretedSortEnumerator */


/** FunctionEnumerator 
* This enumerates function values, based on the enumerator for the
* array type corresponding to the given function type.
*/
class FunctionEnumerator : public TypeEnumeratorBase<FunctionEnumerator> {
public:
  FunctionEnumerator(TypeNode type, TypeEnumeratorProperties * tep = NULL) :
    TypeEnumeratorBase<FunctionEnumerator>(type),
    d_arrayEnum(TheoryBuiltinRewriter::getArrayTypeForFunctionType(type), tep) {
    Assert(type.getKind() == kind::FUNCTION_TYPE);
    d_bvl = NodeManager::currentNM()->getBoundVarListForFunctionType( type );
  }
  /** get the current term of the enumerator */
  Node operator*() {
    if(isFinished()) {
      throw NoMoreValuesException(getType());
    }
    Node a = *d_arrayEnum;
    return TheoryBuiltinRewriter::getLambdaForArrayRepresentation( a, d_bvl );
  }
  /** increment the enumerator */
  FunctionEnumerator& operator++() throw() {
    ++d_arrayEnum;
    return *this;
  }
  /** is the enumerator finished? */
  bool isFinished() throw() {
    return d_arrayEnum.isFinished();
  }
private:
  /** type properties */
  TypeEnumeratorProperties * d_tep;
  /** enumerates arrays, which we convert to functions */
  TypeEnumerator d_arrayEnum;
  /** the bound variable list for the function type we are enumerating.
  * All terms output by this enumerator are of the form (LAMBDA d_bvl t) for some term t.
  */
  Node d_bvl;
};/* class FunctionEnumerator */



}/* CVC4::theory::builtin namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BUILTIN_TYPE_ENUMERATOR_H */
