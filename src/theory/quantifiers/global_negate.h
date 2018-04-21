/*********************                                                        */
/*! \file global_negate.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief global_negate
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__GLOBAL_NEGATE_H
#define __CVC4__THEORY__QUANTIFIERS__GLOBAL_NEGATE_H

#include <vector>
#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** GlobalNegate
 *
 * This class updates a set of assertions to be equivalent to the negation of
 * these assertions. In detail, if assertions is:
 *    F1, ..., Fn
 * then we update this vector to:
 *    forall x1...xm. ~( F1 ^ ... ^ Fn ), true, ..., true
 * where x1...xm are the free variables of F1...Fn.
 */
class GlobalNegate
{
 public:
  GlobalNegate() {}
  ~GlobalNegate() {}
  /** simplify assertions
   *
   * Replaces assertions with a set of assertions that is equivalent to its
   * negation.
   */
  void simplify(std::vector<Node>& assertions);
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__GLOBAL_NEGATE_H */
