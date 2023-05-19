/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Dejan Jovanovic, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Iterator class for equality engine.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__UF__EQUALITY_ENGINE_ITERATOR_H
#define CVC5__THEORY__UF__EQUALITY_ENGINE_ITERATOR_H

#include "expr/node.h"
#include "theory/uf/equality_engine_types.h"

namespace cvc5::internal {
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
}  // namespace cvc5::internal

#endif
