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
 * Branch and bound for arithmetic
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__BRANCH_AND_BOUND__H
#define CVC5__THEORY__ARITH__BRANCH_AND_BOUND__H

#include <map>

#include "expr/node.h"
#include "util/rational.h"
#include "proof/proof_node_manager.h"
#include "proof/trust_node.h"

namespace cvc5 {
namespace theory {
namespace arith {

class BranchAndBound
{
 public:
  BranchAndBound(ProofNodeManager * pnm);
  ~BranchAndBound() {}
  /** 
   * Branch variable, called when integer var has given value
   * in the current model, returns a split to eliminate this model.
   */
  TrustNode branchVariable(TNode var, Rational value);
private:
  /** Proof node manager */
  ProofNodeManager * d_pnm;
};

}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif
