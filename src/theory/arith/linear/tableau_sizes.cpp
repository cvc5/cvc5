/******************************************************************************
 * Top contributors (to current version):
 *   Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "base/output.h"
#include "theory/arith/linear/tableau_sizes.h"
#include "theory/arith/linear/tableau.h"

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

uint32_t TableauSizes::getRowLength(ArithVar b) const {
  return d_tab->basicRowLength(b);
}

uint32_t TableauSizes::getColumnLength(ArithVar x) const {
  return d_tab->getColLength(x);
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
