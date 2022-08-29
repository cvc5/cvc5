/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sygus to builtin
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS__PRINT_SYGUS_TO_BUILTIN_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS__PRINT_SYGUS_TO_BUILTIN_H

#include <map>

#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

Node getPrintableSygusToBuiltin(Node n);

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__SYGUS__TYPE_INFO_H */
