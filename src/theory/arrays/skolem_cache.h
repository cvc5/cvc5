/*********************                                                        */
/*! \file skolem_cache.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Arrays skolem cache
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARRAYS__SKOLEM_CACHE_H
#define CVC4__THEORY__ARRAYS__SKOLEM_CACHE_H

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace arrays {

/**
 * The arrays skolem cache, which provides static methods for constructing
 * skolems with witness forms.
 */
class SkolemCache
{
 public:
  SkolemCache();
  ~SkolemCache() {}

  /**
   * Get the skolem correspoding to the index that witnesses the disequality
   * deq between arrays a and b. The witness form of this skolem is:
   * (witness ((x T)) (=> (not (= a b)) (not (= (select a x) (select b x)))))
   * This skolem is unique for deq, calling this method will always return the
   * same skolem over the lifetime of deq.
   */
  static Node getExtIndexSkolem(Node deq);

 private:
  /**
   * Get the bound variable x of the witness term above for disequality deq
   * between arrays.
   */
  static Node getExtIndexVar(Node deq);
};

}  // namespace arrays
}  // namespace theory
}  // namespace CVC4

#endif
