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
 * Sparse matrix implementations for different types.
 */

#include "theory/arith/linear/matrix.h"

using namespace std;
namespace cvc5::internal {
namespace theory {
namespace arith::linear {

void NoEffectCCCB::update(RowIndex ridx, ArithVar nb, int oldSgn, int currSgn) {}
void NoEffectCCCB::multiplyRow(RowIndex ridx, int sgn){}
bool NoEffectCCCB::canUseRow(RowIndex ridx) const { return false; }

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
