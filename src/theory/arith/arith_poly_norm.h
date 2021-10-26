/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arithmetic utility for polynomial normalization
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__POLY_NORM_H
#define CVC5__THEORY__ARITH__POLY_NORM_H

#include "expr/node.h"

namespace cvc5 {
namespace theory {
namespace arith {

bool isArithPolyNorm(Node n, Node p);

Node arithPolyNorm(Node n);

}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__ARITH__POLY_NORM_H */
