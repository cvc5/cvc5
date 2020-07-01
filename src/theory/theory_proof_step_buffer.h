/*********************                                                        */
/*! \file theory_proof_step_buffer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Theory proof step buffer utility.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__THEORY_PROOF_STEP_BUFFER_H
#define CVC4__THEORY__THEORY_PROOF_STEP_BUFFER_H

#include <vector>

#include "expr/node.h"
#include "expr/proof_step_buffer.h"
#include "theory/builtin/proof_checker.h"

namespace CVC4 {
namespace theory {
/**
 * Class used to speculatively try and buffer a set of proof steps before
 * sending them to a proof object, extended with theory-specfic proof rule
 * utilities.
 */
class TheoryProofStepBuffer : public ProofStepBuffer
{
 public:
  TheoryProofStepBuffer(ProofChecker* pc = nullptr);
  ~TheoryProofStepBuffer() {}
  //---------------------------- utilities builtin proof rules
  /**
   * Apply predicate transform. If this method returns true, it adds (at most
   * one) proof step to the buffer that conclude tgt from premises src, exp. In
   * particular, it may attempt to apply MACRO_SR_PRED_TRANSFORM. This method
   * should be applied when src and tgt are equivalent formulas assuming exp.
   */
  bool applyPredTransform(Node src,
                          Node tgt,
                          const std::vector<Node>& exp,
                          MethodId ids = MethodId::SB_DEFAULT,
                          MethodId idr = MethodId::RW_REWRITE);
  /**
   * Apply predicate introduction. If this method returns true, it adds proof
   * step(s) to the buffer that conclude tgt from premises exp. In particular,
   * it may attempt to apply the rule MACRO_SR_PRED_INTRO. This method should be
   * applied when tgt is equivalent to true assuming exp.
   */
  bool applyPredIntro(Node tgt,
                      const std::vector<Node>& exp,
                      MethodId ids = MethodId::SB_DEFAULT,
                      MethodId idr = MethodId::RW_REWRITE);
  /**
   * Apply predicate elimination. This method returns the result of applying
   * the rule MACRO_SR_PRED_ELIM on src, exp. The returned formula is equivalent
   * to src assuming exp. If the return value is equivalent to src, then no
   * proof step is added to this buffer, since this step is a no-op in this
   * case.
   *
   * Notice that in contrast to the other rules above, predicate elimination
   * never fails and proves a formula that is not explicitly given as an
   * argument tgt. Thus, the return value of this method is Node not bool.
   */
  Node applyPredElim(Node src,
                     const std::vector<Node>& exp,
                     MethodId ids = MethodId::SB_DEFAULT,
                     MethodId idr = MethodId::RW_REWRITE);
  //---------------------------- end utilities builtin proof rules
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__THEORY_PROOF_STEP_BUFFER_H */
