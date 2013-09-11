/*********************                                                        */
/*! \file type_enumerator.h
 ** \verbatim
 ** Original author: Tianyi Liang
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Enumerators for strings
 **
 ** Enumerators for strings.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__STRINGS__TYPE_ENUMERATOR_H
#define __CVC4__THEORY__STRINGS__TYPE_ENUMERATOR_H

#include <sstream>

#include "util/regexp.h"
#include "theory/type_enumerator.h"
#include "expr/type_node.h"
#include "expr/kind.h"

namespace CVC4 {
namespace theory {
namespace strings {

class StringEnumerator : public TypeEnumeratorBase<StringEnumerator> {
  unsigned d_int;

public:

  StringEnumerator(TypeNode type) throw(AssertionException) :
    TypeEnumeratorBase<StringEnumerator>(type),
    d_int(0) {
    Assert(type.getKind() == kind::TYPE_CONSTANT &&
           type.getConst<TypeConstant>() == STRING_TYPE);
  }

  Node operator*() throw() {
    std::stringstream ss;
    ss << d_int;
    return NodeManager::currentNM()->mkConst( ::CVC4::String( ss.str() ) );
  }

  StringEnumerator& operator++() throw() {
    d_int++;
    return *this;
  }

  bool isFinished() throw() {
    return false;
  }

};/* class StringEnumerator */

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__STRINGS__TYPE_ENUMERATOR_H */
