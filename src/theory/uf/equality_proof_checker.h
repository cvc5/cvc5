/*********************                                                        */
/*! \file equality_proof_checker.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Equality proof checker utility
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__UF__EQUALITY_PROOF_CHECKER_H
#define CVC4__THEORY__UF__EQUALITY_PROOF_CHECKER_H

#include "expr/node.h"
#include "expr/proof_checker.h"
#include "expr/proof_node.h"

namespace CVC4 {
namespace theory {
namespace eq {

/** A checker for builtin proofs */
class EqProofChecker : public ProofStepChecker
{
 public:
  EqProofChecker(){}
  ~EqProofChecker(){}
  /** Return the conclusion of pn, or null if it is invalid */
  Node check(ProofStep id,
    const std::vector<std::shared_ptr<ProofNode>>& children,
    const std::vector<Node>& args) override;
  /** Apply substitution */
  static Node applySubstitution(Node n, const std::vector<Node>& exp);
};

}  // namespace eq
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__UF__EQUALITY_PROOF_CHECKER_H */
