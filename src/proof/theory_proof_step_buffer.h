/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Theory proof step buffer utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__THEORY_PROOF_STEP_BUFFER_H
#define CVC5__PROOF__THEORY_PROOF_STEP_BUFFER_H

#include <vector>

#include "expr/node.h"
#include "proof/proof_step_buffer.h"
#include "theory/builtin/proof_checker.h"

namespace cvc5::internal {
/**
 * Class used to speculatively try and buffer a set of proof steps before
 * sending them to a proof object, extended with theory-specfic proof rule
 * utilities.
 */
class TheoryProofStepBuffer : public ProofStepBuffer
{
 public:
  TheoryProofStepBuffer(ProofChecker* pc = nullptr,
                        bool ensureUnique = false,
                        bool autoSym = true);
  ~TheoryProofStepBuffer() {}
  //---------------------------- utilities builtin proof rules
  /**
   * Apply equality introduction. If this method returns true, it adds proof
   * step(s) to the buffer that conclude (= src tgt) from premises exp. In
   * particular, it may attempt to apply the rule MACRO_SR_EQ_INTRO. This
   * method should be applied when tgt is equivalent to src assuming exp.
   *
   * @param useExpected If true, we pass (= src tgt) as expected to tryStep.
   * When true, this method will always succeed if proof checking is
   * disabled.
   */
  bool applyEqIntro(Node src,
                    Node tgt,
                    const std::vector<Node>& exp,
                    MethodId ids = MethodId::SB_DEFAULT,
                    MethodId ida = MethodId::SBA_SEQUENTIAL,
                    MethodId idr = MethodId::RW_REWRITE,
                    bool useExpected = false);
  /**
   * Apply predicate transform. If this method returns true, it adds (at most
   * one) proof step to the buffer that conclude tgt from premises src, exp. In
   * particular, it may attempt to apply MACRO_SR_PRED_TRANSFORM. This method
   * should be applied when src and tgt are equivalent formulas assuming exp.
   *
   * @param useExpected If true, we pass tgt as expected to tryStep.
   * When true, this method will always succeed if proof checking is
   * disabled.
   */
  bool applyPredTransform(Node src,
                          Node tgt,
                          const std::vector<Node>& exp,
                          MethodId ids = MethodId::SB_DEFAULT,
                          MethodId ida = MethodId::SBA_SEQUENTIAL,
                          MethodId idr = MethodId::RW_REWRITE,
                          bool useExpected = false);
  /**
   * Apply predicate introduction. If this method returns true, it adds proof
   * step(s) to the buffer that conclude tgt from premises exp. In particular,
   * it may attempt to apply the rule MACRO_SR_PRED_INTRO. This method should be
   * applied when tgt is equivalent to true assuming exp.
   *
   * @param useExpected If true, we pass tgt as expected to tryStep.
   * When true, this method will always succeed if proof checking is
   * disabled.
   */
  bool applyPredIntro(Node tgt,
                      const std::vector<Node>& exp,
                      MethodId ids = MethodId::SB_DEFAULT,
                      MethodId ida = MethodId::SBA_SEQUENTIAL,
                      MethodId idr = MethodId::RW_REWRITE,
                      bool useExpected = false);
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
                     MethodId ida = MethodId::SBA_SEQUENTIAL,
                     MethodId idr = MethodId::RW_REWRITE);
  //---------------------------- end utilities builtin proof rules

  //---------------------------- utility methods for normalizing clauses
  /**
   * Normalizes a non-unit clause (an OR node) according to factoring and
   * reordering, i.e. removes duplicates and reorders literals (according to
   * node ids). Moreover it eliminates double negations, which can be done also
   * for unit clauses (a arbitrary Boolean node). All normalization steps are
   * tracked via proof steps added to this proof step buffer.
   *
   * @param n the clause to be normalized
   * @return the normalized clause node
   */
  Node factorReorderElimDoubleNeg(Node n);

  /**
   * Eliminates double negation of a literal if it has the form
   *  (not (not t))
   * If the elimination happens, a step is added to this proof step buffer.
   *
   * @param n the node to have the top-level double negation eliminated
   * @return the normalized clause node
   */
  Node elimDoubleNegLit(Node n);
};

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__THEORY_PROOF_STEP_BUFFER_H */
