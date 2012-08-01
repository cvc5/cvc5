/*********************                                                        */
/*! \file type_enumerator.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief An enumerator for arrays
 **
 ** An enumerator for arrays.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARRAYS__TYPE_ENUMERATOR_H
#define __CVC4__THEORY__ARRAYS__TYPE_ENUMERATOR_H

#include "theory/type_enumerator.h"
#include "expr/type_node.h"
#include "expr/kind.h"

namespace CVC4 {
namespace theory {
namespace arrays {

class ArrayEnumerator : public TypeEnumeratorBase<ArrayEnumerator> {
  TypeEnumerator d_index;
  TypeEnumerator d_constituent;

public:

  ArrayEnumerator(TypeNode type) throw(AssertionException) :
    TypeEnumeratorBase<ArrayEnumerator>(type),
    d_index(TypeEnumerator(type.getArrayIndexType())),
    d_constituent(TypeEnumerator(type.getArrayConstituentType())) {
  }

  Node operator*() throw(NoMoreValuesException) {
    return Node::null();
    //return NodeManager::currentNM()->mkConst(Array(d_size, d_bits));
  }

  ArrayEnumerator& operator++() throw() {
    return *this;
  }

};/* class ArrayEnumerator */

}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARRAYS__TYPE_ENUMERATOR_H */
