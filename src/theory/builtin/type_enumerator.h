/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Enumerator for uninterpreted sorts and functions.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BUILTIN__TYPE_ENUMERATOR_H
#define CVC5__THEORY__BUILTIN__TYPE_ENUMERATOR_H

#include "expr/kind.h"
#include "expr/type_node.h"
#include "theory/type_enumerator.h"
#include "util/integer.h"

namespace cvc5::internal {
namespace theory {
namespace builtin {

class UninterpretedSortEnumerator : public TypeEnumeratorBase<UninterpretedSortEnumerator> {
  Integer d_count;
  bool d_has_fixed_bound;
  Integer d_fixed_bound;

 public:
  UninterpretedSortEnumerator(TypeNode type,
                              TypeEnumeratorProperties* tep = nullptr);

  Node operator*() override;

  UninterpretedSortEnumerator& operator++() override;

  bool isFinished() override;
};

}  // namespace builtin
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BUILTIN_TYPE_ENUMERATOR_H */
