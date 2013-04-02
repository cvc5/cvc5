/*********************                                                        */
/*! \file type_enumerator.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Enumerator for uninterpreted sorts
 **
 ** Enumerator for uninterpreted sorts.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BUILTIN__TYPE_ENUMERATOR_H
#define __CVC4__THEORY__BUILTIN__TYPE_ENUMERATOR_H

#include "util/integer.h"
#include "util/uninterpreted_constant.h"
#include "theory/type_enumerator.h"
#include "expr/type_node.h"
#include "expr/kind.h"

namespace CVC4 {
namespace theory {
namespace builtin {

class UninterpretedSortEnumerator : public TypeEnumeratorBase<UninterpretedSortEnumerator> {
  Integer d_count;

public:

  UninterpretedSortEnumerator(TypeNode type) throw(AssertionException) :
    TypeEnumeratorBase<UninterpretedSortEnumerator>(type),
    d_count(0) {
    Assert(type.getKind() == kind::SORT_TYPE);
  }

  Node operator*() throw() {
    return NodeManager::currentNM()->mkConst(UninterpretedConstant(getType().toType(), d_count));
  }

  UninterpretedSortEnumerator& operator++() throw() {
    d_count += 1;
    return *this;
  }

  bool isFinished() throw() {
    return false;
  }

};/* class UninterpretedSortEnumerator */

}/* CVC4::theory::builtin namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BUILTIN_TYPE_ENUMERATOR_H */
