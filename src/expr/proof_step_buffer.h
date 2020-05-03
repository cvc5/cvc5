/*********************                                                        */
/*! \file proof_step_buffer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Inference to proof conversion
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__PROOF_STEP_BUFFER_H
#define CVC4__EXPR__PROOF_STEP_BUFFER_H

#include <vector>

#include "expr/node.h"
#include "expr/proof_checker.h"
#include "expr/proof_rule.h"
#include "expr/proof.h"

namespace CVC4 {

/**
 * Class used to speculatively try and buffer a set of proof steps before
 * sending them to a proof object.
 */
class ProofStepBuffer
{
 public:
  ProofStepBuffer(CDProof * pf);
  ~ProofStepBuffer() {}
  /**
   * Returns the conclusion of the proof step, as determined by the proof
   * checker of the given proof. If this is non-null, then the given step
   * is added to the buffer maintained by this class.
   * 
   * If expected is non-null, then this method returns null if the result of
   * checking is not equal to expected.
   */
  Node tryStep(PfRule id, const std::vector<Node>& children, const std::vector<Node>& args,
             Node expected = Node::null());
  /**
   * Add all buffered proof steps into the underlying proof object.
   */
  bool addTo(CDProof * pf);
  /** Clear */
  void clear();
 private:
  /** The proof checker*/
  ProofChecker* d_checker;
  /** the queued proof steps */
  std::vector<std::pair<Node,ProofStep>> d_steps;
};

}  // namespace CVC4

#endif /* CVC4__EXPR__PROOF_STEP_BUFFER_H */
