/*********************                                                        */
/*! \file proof_checker.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Proof checker utility
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__PROOF_CHECKER_H
#define CVC4__EXPR__PROOF_CHECKER_H

#include <map>

#include "expr/node.h"
#include "expr/proof_node.h"

namespace CVC4 {
  
/** A virtual base class for checking proofs */
class ProofStepChecker
{
 public:
  ProofStepChecker(){}
  ~ProofStepChecker(){}
  /** Check
   * 
   * Return the formula that is proven by proof node with the given id, children
   * and arguments, or null if such a node is not well-formed.
   */
  virtual Node check(ProofStep id,
    const std::vector<std::shared_ptr<ProofNode>>& children,
    const std::vector<Node>& args) = 0;
};

/** A class for checking proofs */
class ProofChecker
{
public:
  ProofChecker() {}
  ~ProofChecker() {}
  /** Check
   * 
   * Return the formula that is proven by proof node pn, or null if pn is not
   * well-formed.
   */
  Node check(ProofNode * pn);
  /** Indicate that psc is the checker for proof step id */
  void registerChecker( ProofStep id, ProofStepChecker * psc );
private:
  /** Maps proof steps to their checker */
  std::map< ProofStep, ProofStepChecker * > d_checker;
};

}  // namespace CVC4

#endif /* CVC4__EXPR__PROOF_CHECKER_H */
