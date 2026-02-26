/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
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

void NoEffectCCCB::update(CVC5_UNUSED RowIndex ridx,
                          CVC5_UNUSED ArithVar nb,
                          CVC5_UNUSED int oldSgn,
                          CVC5_UNUSED int currSgn)
{
}
void NoEffectCCCB::multiplyRow(CVC5_UNUSED RowIndex ridx, CVC5_UNUSED int sgn)
{
}
bool NoEffectCCCB::canUseRow(CVC5_UNUSED RowIndex ridx) const { return false; }

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
