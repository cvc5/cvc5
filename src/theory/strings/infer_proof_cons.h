/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Inference to proof conversion.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__INFER_PROOF_CONS_H
#define CVC5__THEORY__STRINGS__INFER_PROOF_CONS_H

#include <vector>

#include "cvc5/cvc5_proof_rule.h"
#include "expr/node.h"
#include "expr/term_context.h"
#include "proof/conv_proof_generator.h"
#include "proof/proof_checker.h"
#include "proof/theory_proof_step_buffer.h"
#include "smt/env_obj.h"
#include "theory/builtin/proof_checker.h"
#include "theory/strings/infer_info.h"
#include "theory/strings/sequences_stats.h"
#include "theory/uf/proof_equality_engine.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

class StringCoreTermContext : public TermContext
{
 public:
  StringCoreTermContext();
  /** The initial value: valid. */
  uint32_t initialValue() const override;
  /** Compute the value of the index^th child of t whose hash is tval */
  uint32_t computeValue(TNode t, uint32_t tval, size_t index) const override;
};

/**
 * Converts between the strings-specific (untrustworthy) InferInfo class and
 * information about how to construct a trustworthy proof step
 * (ProofRule, children, args). It acts as a (lazy) proof generator where the
 * former is registered via notifyFact and the latter is asked for in
 * getProofFor, typically by the proof equality engine.
 *
 * The main (private) method of this class is convert below, which is
 * called when we need to construct a proof node from an InferInfo.
 *
 * This class uses lazy proof reconstruction. Namely, the getProofFor method
 * returns applications of the rule MACRO_STRING_INFERENCE, which store the
 * arguments to the proof conversion routine "convert" below.
 */
class InferProofCons : protected EnvObj, public ProofGenerator
{
  typedef context::CDHashMap<Node, std::shared_ptr<InferInfo>> NodeInferInfoMap;

 public:
  InferProofCons(Env& env,
                 context::Context* c,
                 SequencesStatistics& statistics);
  ~InferProofCons() {}
  /**
   * This is called to notify that ii is an inference that may need a proof
   * in the future.
   *
   * In detail, this class should be prepared to respond to a call to:
   *   getProofFor(ii.d_conc)
   * in the remainder of the SAT context. This method copies ii and stores it
   * in the context-dependent map d_lazyFactMap below.
   *
   * This is used for lazy proof construction, where proofs are constructed
   * only for facts that are explained.
   */
  void notifyFact(const InferInfo& ii);
  /**
   * Same as above, but always overwrites. This is used for lemmas and
   * conflicts, which do not necessarily have unique conclusions.
   */
  void notifyLemma(const InferInfo& ii);

  /**
   * This returns the proof for fact. This is required for using this class as
   * a lazy proof generator.
   *
   * It should be the case that a call was made to notifyFact(ii) where
   * ii.d_conc is fact in this SAT context.
   *
   * This returns the appropriate application of MACRO_STRING_INFERENCE so that
   * it can be reconstructed if necessary during proof post-processing.
   */
  std::shared_ptr<ProofNode> getProofFor(Node fact) override;
  /** Identify this generator (for debugging, etc..) */
  virtual std::string identify() const override;
  /**
   * Pack arguments of a MACRO_STRING_INFERENCE rule application in args. This
   * proof rule stores the arguments to the convert method of this class below.
   */
  static void packArgs(Node conc,
                       InferenceId infer,
                       bool isRev,
                       const std::vector<Node>& exp,
                       std::vector<Node>& args);
  /**
   * Inverse of the above method, which recovers the arguments that were packed
   * into the vector args.
   */
  static bool unpackArgs(const std::vector<Node>& args,
                         Node& conc,
                         InferenceId& infer,
                         bool& isRev,
                         std::vector<Node>& exp);

  /** convert
   *
   * Add proof of running convert on the given arguments to CDProof pf. This is
   * called lazily during proof post-processing.
   *
   * This method is called when the theory of strings makes an inference
   * described by an InferInfo, whose fields are given by the first four
   * arguments of this method.
   *
   * This method converts this call to instructions on what the proof rule
   * step(s) are for concluding the conclusion of the inference. This
   * information is either:
   *
   * (A) stored in the argument ps, which consists of:
   * - A proof rule identifier (ProofStep::d_rule).
   * - The premises of the proof step (ProofStep::d_children).
   * - Arguments to the proof step (ProofStep::d_args).
   *
   * (B) If the proof for the inference cannot be captured by a single
   * step, then the d_rule field of ps is not set, and useBuffer is set to
   * true. In this case, the argument psb is updated to contain (possibly
   * multiple) proof steps for how to construct a proof for the given inference.
   * In particular, psb will contain a set of steps that form a proof
   * whose conclusion is conc and whose free assumptions are exp.
   */
  static bool convert(Env& env,
                      InferenceId infer,
                      bool isRev,
                      Node conc,
                      const std::vector<Node>& exp,
                      CDProof* pf);

 private:
  /**
   * Convert length proof. If this method returns true, it adds proof step(s)
   * to the buffer psb that conclude lenReq from premises lenExp.
   */
  static bool convertLengthPf(Node lenReq,
                              const std::vector<Node>& lenExp,
                              TheoryProofStepBuffer& psb);
  /**
   * Helper method, adds the proof of (TRANS eqa eqb) into the proof step
   * buffer psb, where eqa and eqb are flipped as needed. Returns the
   * conclusion, or null if we were not able to construct a TRANS step.
   */
  static Node convertTrans(Node eqa, Node eqb, TheoryProofStepBuffer& psb);

  /** The lazy fact map */
  NodeInferInfoMap d_lazyFactMap;
  /** Reference to the statistics for the theory of strings/sequences. */
  SequencesStatistics& d_statistics;
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__INFER_PROOF_CONS_H */
