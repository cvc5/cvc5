/*********************                                                        */
/*! \file proof_node_algorithm.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Proof node algorithm utilities.
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__PROOF_NODE_ALGORITHM_H
#define CVC4__EXPR__PROOF_NODE_ALGORITHM_H

#include <vector>

#include "expr/node.h"
#include "expr/proof_node.h"

namespace CVC4 {
namespace expr {

/**
 * This adds to the vector assump all formulas that are "free assumptions" of
 * the proof whose root is ProofNode pn. A free assumption is a formula F
 * that is an argument (in d_args) of a ProofNode whose kind is ASSUME, and
 * that proof node is not beneath an application of SCOPE containing F as an
 * argument.
 *
 * This traverses the structure of the dag represented by this ProofNode.
 * Its implementation is analogous to expr::getFreeVariables.
 *
 * @param pn The proof node.
 * @param assump The vector to add the free asumptions of pn to.
 */
void getFreeAssumptions(ProofNode* pn, std::vector<Node>& assump);
/**
 * Same as above, but maps assumptions to the proof pointer(s) for that
 * assumption. Notice that depending on how pn is constructed, there may be
 * multiple ProofNode that are ASSUME proofs of the same assumption, which
 * are each added to the range of the assumption.
 *
 * @param pn The proof node.
 * @param amap The mapping to add the free asumptions of pn and their
 * corresponding proof nodes to.
 */
void getFreeAssumptionsMap(
    std::shared_ptr<ProofNode> pn,
    std::map<Node, std::vector<std::shared_ptr<ProofNode>>>& amap);

}  // namespace expr
}  // namespace CVC4

#endif /* CVC4__EXPR__PROOF_NODE_ALGORITHM_H */
