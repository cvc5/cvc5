/*********************                                                        */
/*! \file equality_engine_iterator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Andrew Reynolds, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Iterator class for equality engine
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__UF__EQUALITY_ENGINE_ITERATOR_H
#define CVC4__THEORY__UF__EQUALITY_ENGINE_ITERATOR_H

#include "expr/node.h"
#include "theory/uf/equality_engine_types.h"

namespace CVC4 {
namespace theory {
namespace eq {

class EqualityEngine;

/**
 * Iterator to iterate over all the equivalence classes in an equality engine.
 */
class EqClassesIterator
{
 public:
  EqClassesIterator();
  EqClassesIterator(const eq::EqualityEngine* ee);
  Node operator*() const;
  bool operator==(const EqClassesIterator& i) const;
  bool operator!=(const EqClassesIterator& i) const;
  EqClassesIterator& operator++();
  EqClassesIterator operator++(int);
  bool isFinished() const;

 private:
  /** Pointer to the equality engine we are iterating over */
  const eq::EqualityEngine* d_ee;
  /** The iterator value */
  size_t d_it;
};

/**
 * Iterator to iterate over the equivalence class members in a particular
 * equivalence class.
 */
class EqClassIterator
{
 public:
  EqClassIterator();
  /**
   * Iterate over equivalence class eqc, where eqc must be a representative of
   * argument ee.
   */
  EqClassIterator(Node eqc, const eq::EqualityEngine* ee);
  Node operator*() const;
  bool operator==(const EqClassIterator& i) const;
  bool operator!=(const EqClassIterator& i) const;
  EqClassIterator& operator++();
  EqClassIterator operator++(int);
  bool isFinished() const;

 private:
  /** Pointer to the equality engine we are iterating over */
  const eq::EqualityEngine* d_ee;
  /** Starting node */
  EqualityNodeId d_start;
  /** Current node */
  EqualityNodeId d_current;
};

}  // Namespace eq
}  // Namespace theory
}  // Namespace CVC4

#endif
