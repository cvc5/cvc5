/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Enumerator for functions.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__UF__TYPE_ENUMERATOR_H
#define CVC5__THEORY__UF__TYPE_ENUMERATOR_H

#include "expr/kind.h"
#include "expr/type_node.h"
#include "theory/type_enumerator.h"
#include "util/integer.h"

namespace cvc5::internal {
namespace theory {
namespace uf {

/** FunctionEnumerator
 * This enumerates function values, based on the enumerator for the
 * array type corresponding to the given function type.
 */
class FunctionEnumerator : public TypeEnumeratorBase<FunctionEnumerator>
{
 public:
  FunctionEnumerator(TypeNode type, TypeEnumeratorProperties* tep = nullptr);
  /** Get the current term of the enumerator. */
  Node operator*() override;
  /** Increment the enumerator. */
  FunctionEnumerator& operator++() override;
  /** is the enumerator finished? */
  bool isFinished() override { return d_arrayEnum.isFinished(); }

 private:
  /** Enumerates arrays, which we convert to functions. */
  TypeEnumerator d_arrayEnum;
}; /* class FunctionEnumerator */

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__UF__TYPE_ENUMERATOR_H */
