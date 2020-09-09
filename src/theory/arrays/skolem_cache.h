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
 * The arrays inference manager.
 */
class SkolemCache
{
 public:
  SkolemCache();
  ~SkolemCache() {}

  /**
   * Get the skolem correspoding to the index that witnesses the disequality
   * between arrays a and b.
   */
  static Node getExtIndexSkolem(Node a, Node b);

 private:
  /** Get the bound variable */
  static Node getExtIndexVar(Node a, Node b);
};

}  // namespace arrays
}  // namespace theory
}  // namespace CVC4

#endif
