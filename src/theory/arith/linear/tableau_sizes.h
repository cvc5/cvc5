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

#include "cvc5_private.h"

#pragma once

#include "theory/arith/linear/arithvar.h"

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

class Tableau;

class TableauSizes {
private:
  const Tableau* d_tab;
public:
  TableauSizes(const Tableau* tab): d_tab(tab){}

  uint32_t getRowLength(ArithVar b) const;
  uint32_t getColumnLength(ArithVar x) const;
}; /* TableauSizes */

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
