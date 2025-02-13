/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
   * @param env Reference to the environment.
   * @param infer The inference id.
   * @param isRev Whether this was the reverse form of the inference id.
   * @param conc The conclusion of the inference.
   * @param exp The explanation of the inference.
   * @param pf The proof to add to.
   * @return true if we successfully added a proof of conc to pf, whose free
   * assumptions are a subset of exp.
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
  /**
   * Helper method for convert. Concludes tgt from src, using AND_ELIM
   * if necessary.
   * @param nm Pointer to the node manager.
   * @param src The source predicate, assumed to have a proof in psb.
   * @param tgt The target predicate.
   * @param psb The proof step buffer.
   * @return true if we guarantee psb has a proof of tgt.
   */
  static bool convertAndElim(NodeManager* nm,
                             const Node& src,
                             const Node& tgt,
                             TheoryProofStepBuffer& psb);
  /**
   * Helper method for convert.
   * Convert core substitution. This is used to apply a
   * substitution given by exp to src. The indices determine
   * which contexts to apply the substitution to apply, based
   * on the definition of StringCoreTermContext.
   * We add a proof of src = src' to pf, where src' is the result
   * of applying the substitution to src'.
   * If proveSrc is false, we add a proof of src' given free
   * assumption src to psb. Otherwise we add a proof of src given
   * free assumption src' to psb.
   * @param env Reference to the environment
   * @param pf Pointer to proof.
   * @param psb Reference to proof step buffer.
   * @param src The predicate to apply the substitution to.
   * @param exp A list of equalities defining the substitution.
   * @param minIndex The minimum term context value to consider.
   * @param maxIndex The maximum term context value to consider.
   * @param proveSrc Whether we prove src from src' or vice versa.
   * @return The result of applying the substituion to src.
   */
  static Node convertCoreSubs(Env& env,
                              CDProof* pf,
                              TheoryProofStepBuffer& psb,
                              const Node& src,
                              const std::vector<Node>& exp,
                              size_t minIndex = 0,
                              size_t maxIndex = 0,
                              bool proveSrc = false);
  /**
   * This method ensures that constants in eq have been spliced to match
   * the requirements of the given proof rule (possibly in its reverse form).
   * If necessary, we rewrite eq to a new equality eqr and add a proof of eqr
   * from eq as a step to psb and return eqr. Otherwise, eq is returned.
   * @param env Reference to the environment
   * @param psb Reference to proof step buffer.
   * @param rule The rule whose premise is eq.
   * @param eq The equality to ensure constants are spliced in.
   * @param conc The target conclusion of the rule, used if rule is
   * CONCAT_UNIFY.
   * @param isRev Whether rule is being applied in the reverse direction.
   * @return The result of splicing the appropriate constants (if any) in eq.
   */
  static Node spliceConstants(Env& env,
                              ProofRule rule,
                              TheoryProofStepBuffer& psb,
                              const Node& eq,
                              const Node& conc,
                              bool isRev);
  /** The lazy fact map */
  NodeInferInfoMap d_lazyFactMap;
  /** Reference to the statistics for the theory of strings/sequences. */
  SequencesStatistics& d_statistics;
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__INFER_PROOF_CONS_H */
