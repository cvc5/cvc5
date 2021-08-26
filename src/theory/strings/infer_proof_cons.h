/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

#include "expr/node.h"
#include "proof/proof_checker.h"
#include "proof/proof_rule.h"
#include "proof/theory_proof_step_buffer.h"
#include "theory/builtin/proof_checker.h"
#include "theory/strings/infer_info.h"
#include "theory/strings/sequences_stats.h"
#include "theory/uf/proof_equality_engine.h"

namespace cvc5 {
namespace theory {
namespace strings {

/**
 * Converts between the strings-specific (untrustworthy) InferInfo class and
 * information about how to construct a trustworthy proof step
 * (PfRule, children, args). It acts as a (lazy) proof generator where the
 * former is registered via notifyFact and the latter is asked for in
 * getProofFor, typically by the proof equality engine.
 *
 * The main (private) method of this class is convert below, which is
 * called when we need to construct a proof node from an InferInfo.
 */
class InferProofCons : public ProofGenerator
{
  typedef context::CDHashMap<Node, std::shared_ptr<InferInfo>> NodeInferInfoMap;

 public:
  InferProofCons(context::Context* c,
                 ProofNodeManager* pnm,
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
   * This returns the proof for fact. This is required for using this class as
   * a lazy proof generator.
   *
   * It should be the case that a call was made to notifyFact(ii) where
   * ii.d_conc is fact in this SAT context.
   */
  std::shared_ptr<ProofNode> getProofFor(Node fact) override;
  /** Identify this generator (for debugging, etc..) */
  virtual std::string identify() const override;

 private:
  /** convert
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
   * whose conclusion is ii.d_conc and whose free assumptions are ii.d_ant.
   */
  void convert(InferenceId infer,
               bool isRev,
               Node conc,
               const std::vector<Node>& exp,
               ProofStep& ps,
               TheoryProofStepBuffer& psb,
               bool& useBuffer);
  /**
   * Convert length proof. If this method returns true, it adds proof step(s)
   * to the buffer psb that conclude lenReq from premises lenExp.
   */
  bool convertLengthPf(Node lenReq,
                       const std::vector<Node>& lenExp,
                       TheoryProofStepBuffer& psb);
  /**
   * Helper method, adds the proof of (TRANS eqa eqb) into the proof step
   * buffer psb, where eqa and eqb are flipped as needed. Returns the
   * conclusion, or null if we were not able to construct a TRANS step.
   */
  Node convertTrans(Node eqa, Node eqb, TheoryProofStepBuffer& psb);
  /**
   * Purify core substitution.
   *
   * When reconstructing proofs for the core strings calculus, we rely on
   * sequential substitutions for constructing proofs involving recursive
   * computation of normal forms. However, this can be incorrect in cases where
   * a term like (str.replace x a b) is being treated as an atomic term,
   * and a substitution applied over (str.replace x a b) -> c, x -> d.
   * This can lead to the term (str.replace d a b) being generated instead of
   * c.
   *
   * As an example of this method, given input:
   *   tgt = (= x (str.++ (f x) c))
   *   children = { (= (f x) a), (= x (str.++ b (f x))) }
   *   concludeTgtNew = true
   * This method updates:
   *   tgt = (= x (str.++ k c))
   *   children = { (= k a), (= x (str.++ b k)) }
   * where k is the purification skolem for (f x). Additionally, it ensures
   * that psb has a proof of:
   *   (= x (str.++ k c)) from (= x (str.++ (f x) c))
   *      ...note the direction, since concludeTgtNew = true
   *   (= k a) from (= (f x) a)
   *   (= x (str.++ b k)) from (= x (str.++ b (f x)))
   * Notice that the resulting substitution can now be safely used as a
   * sequential substution, since (f x) has been purified with k. The proofs
   * in psb ensure that a proof step involving the purified substitution will
   * have the same net effect as a proof step using the original substitution.
   *
   * @param tgt The term we were originally going to apply the substitution to.
   * @param children The premises corresponding to the substitution.
   * @param psb The proof step buffer
   * @param concludeTgtNew Whether we require proving the purified form of
   * tgt from tgt or vice versa.
   * @return true if we successfully purified the substitution and the target
   * term. Additionally, if successful, we ensure psb contains proofs of
   * children'[i] from children[i] for all i, and tgt' from tgt (or vice versa
   * based on concludeTgtNew).
   */
  bool purifyCoreSubstitution(Node& tgt,
                              std::vector<Node>& children,
                              TheoryProofStepBuffer& psb,
                              bool concludeTgtNew = false) const;
  /**
   * Return the purified form of the predicate lit with respect to a set of
   * terms to purify, call the returned literal lit'.
   * If concludeNew is true, then we add a proof of lit' from lit in psb;
   * otherwise we add a proof of lit from lit'.
   * Note that string predicates that require purification are string
   * (dis)equalities only.
   */
  Node purifyCorePredicate(Node lit,
                           bool concludeNew,
                           TheoryProofStepBuffer& psb,
                           std::unordered_set<Node>& termsToPurify) const;
  /**
   * Purify term with respect to a set of terms to purify. This replaces
   * all terms to purify with their purification variables that occur in
   * positions that are relevant for the core calculus of strings (direct
   * children of concat or equal).
   */
  Node purifyCoreTerm(Node n, std::unordered_set<Node>& termsToPurify) const;
  /** the proof node manager */
  ProofNodeManager* d_pnm;
  /** The lazy fact map */
  NodeInferInfoMap d_lazyFactMap;
  /** Reference to the statistics for the theory of strings/sequences. */
  SequencesStatistics& d_statistics;
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__STRINGS__INFER_PROOF_CONS_H */
