/*********************                                                        */
/*! \file type_enumerator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Mathias Preiner, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief An enumerator for bitvectors
 **
 ** An enumerator for bitvectors.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BV__TYPE_ENUMERATOR_H
#define CVC4__THEORY__BV__TYPE_ENUMERATOR_H

#include "expr/kind.h"
#include "expr/type_node.h"
#include "theory/type_enumerator.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/bitvector.h"
#include "util/integer.h"

namespace CVC4 {
namespace theory {
namespace bv {

class BitVectorEnumerator : public TypeEnumeratorBase<BitVectorEnumerator> {
  size_t d_size;
  Integer d_bits;

public:

  BitVectorEnumerator(TypeNode type, TypeEnumeratorProperties * tep = NULL) :
    TypeEnumeratorBase<BitVectorEnumerator>(type),
    d_size(type.getBitVectorSize()),
    d_bits(0) {
  }

  Node operator*() override
  {
    if(d_bits != d_bits.modByPow2(d_size)) {
      throw NoMoreValuesException(getType());
    }
    return utils::mkConst(d_size, d_bits);
  }

  BitVectorEnumerator& operator++() override
  {
    d_bits += 1;
    return *this;
  }

  bool isFinished() override { return d_bits != d_bits.modByPow2(d_size); }
};/* BitVectorEnumerator */

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__BV__TYPE_ENUMERATOR_H */
