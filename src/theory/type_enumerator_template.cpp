/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Enumerators for types.
 */

#include <sstream>

#include "base/check.h"
#include "expr/kind.h"
#include "theory/type_enumerator.h"

// clang-format off
${type_enumerator_includes}
// clang-format on

using namespace std;

namespace cvc5::internal {
namespace theory {

TypeEnumeratorInterface* TypeEnumerator::mkTypeEnumerator(
    TypeNode type, TypeEnumeratorProperties* tep)
{
  switch (type.getKind())
  {
    case kind::TYPE_CONSTANT:
      switch (type.getConst<TypeConstant>())
      {
        // clang-format off
        ${mk_type_enumerator_type_constant_cases}
          // clang-format on
        default: Unhandled() << "No type enumerator for type `" << type << "'";
      }
      Unreachable();
      // clang-format off
      ${mk_type_enumerator_cases}
      // clang-format on
    default: Unhandled() << "No type enumerator for type `" << type << "'";
  }
  Unreachable();
}

}  // namespace theory
}  // namespace cvc5::internal
