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
 ** \brief An enumerator for bitvectors
 **
 ** An enumerator for bitvectors.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BV__TYPE_ENUMERATOR_H
#define __CVC4__THEORY__BV__TYPE_ENUMERATOR_H

#include "util/bitvector.h"
#include "util/integer.h"
#include "theory/type_enumerator.h"
#include "expr/type_node.h"
#include "expr/kind.h"

namespace CVC4 {
namespace theory {
namespace bv {

class BitVectorEnumerator : public TypeEnumeratorBase<BitVectorEnumerator> {
  size_t d_size;
  Integer d_bits;

public:

  BitVectorEnumerator(TypeNode type) throw(AssertionException) :
    TypeEnumeratorBase(type),
    d_size(type.getBitVectorSize()),
    d_bits(0) {
  }

  Node operator*() throw(NoMoreValuesException) {
    if(d_bits != d_bits.modByPow2(d_size)) {
      throw NoMoreValuesException(getType());
    }
    return NodeManager::currentNM()->mkConst(BitVector(d_size, d_bits));
  }

  BitVectorEnumerator& operator++() throw() {
    d_bits += 1;
    return *this;
  }

};/* BitVectorEnumerator */

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BV__TYPE_ENUMERATOR_H */
