/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Clark Barrett, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An enumerator for arrays.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARRAYS__TYPE_ENUMERATOR_H
#define CVC5__THEORY__ARRAYS__TYPE_ENUMERATOR_H

#include "expr/array_store_all.h"
#include "expr/kind.h"
#include "expr/type_node.h"
#include "theory/rewriter.h"
#include "theory/type_enumerator.h"

namespace cvc5::internal {
namespace theory {
namespace arrays {

class ArrayEnumerator : public TypeEnumeratorBase<ArrayEnumerator>
{
 public:
  /** Constructor. */
  ArrayEnumerator(TypeNode type, TypeEnumeratorProperties* tep = nullptr);

  /**
   * Copy Constructor.
   * An array enumerator could be large, and generally you don't want to
   * go around copying these things; but a copy ctor is presently required
   * by the TypeEnumerator framework.
   */
  ArrayEnumerator(const ArrayEnumerator& ae);

  /** Destructor. */
  ~ArrayEnumerator();

  Node operator*() override;
  ArrayEnumerator& operator++() override;
  bool isFinished() override;

 private:
  TypeEnumeratorProperties* d_tep;
  TypeEnumerator d_index;
  TypeNode d_constituentType;
  NodeManager* d_nm;
  std::vector<Node> d_indexVec;
  std::vector<TypeEnumerator*> d_constituentVec;
  bool d_finished;
  Node d_arrayConst;
}; /* class ArrayEnumerator */

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARRAYS__TYPE_ENUMERATOR_H */
