/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Mathias Preiner, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class representing a Record definition.
 */

#include "cvc5_public.h"

#ifndef CVC5__RECORD_H
#define CVC5__RECORD_H

#include <iostream>
#include <string>
#include <vector>
#include <utility>

// Forward Declarations
namespace cvc5 {
// This forward delcartion is required to resolve a cicular dependency with
// Record which is a referenced in a Kind file.
class TypeNode;
}  // namespace cvc5

namespace cvc5 {

using Record = std::vector<std::pair<std::string, TypeNode>>;

}  // namespace cvc5

#endif /* CVC5__RECORD_H */
