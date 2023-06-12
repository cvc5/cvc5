/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
 * (PfRule, children, args). It acts as a (lazy) proof generator where the
 * former is registered via notifyFact and the latter is asked for in
 * getProofFor, typically by the proof equality engine.
 *
 * The main (private) method of this class is convert below, which is
 * called when we need to construct a proof node from an InferInfo.
 *
 * This class uses lazy proof reconstruction. Namely, the getProofFor method
 * returns applications of the rule STRING_INFERENCE, which store the arguments
 * to the proof conversion routine "convert" below.
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
   * This returns the appropriate application of STRING_INFERENCE so that it
   * can be reconstructed if necessary during proof post-processing.
   */
  std::shared_ptr<ProofNode> getProofFor(Node fact) override;
  /** Identify this generator (for debugging, etc..) */
  virtual std::string identify() const override;
  /**
   * Add proof of running convert on the given arguments to CDProof pf. This is
   * called lazily during proof post-processing.
   */
  static bool convertAndAddProofTo(CDProof* pf,
                                   Node conc,
                                   InferenceId infer,
                                   bool isRev,
                                   const std::vector<Node>& exp);
  /**
   * Pack arguments of a STRING_INFERENCE rule application in args. This proof
   * rule stores the arguments to the convert method of this class below.
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
   * whose conclusion is conc and whose free assumptions are exp.
   */
  static void convert(InferenceId infer,
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
  static bool convertLengthPf(Node lenReq,
                              const std::vector<Node>& lenExp,
                              TheoryProofStepBuffer& psb);
  /**
   * Helper method, adds the proof of (TRANS eqa eqb) into the proof step
   * buffer psb, where eqa and eqb are flipped as needed. Returns the
   * conclusion, or null if we were not able to construct a TRANS step.
   */
  static Node convertTrans(Node eqa, Node eqb, TheoryProofStepBuffer& psb);
  enum class PurifyType
  {
    // we are purifying an equality corresponding to a substitution
    SUBS_EQ,
    // we are purifying a (dis)equality in the core calculus
    CORE_EQ,
    // we are purifying a equality or predicate for extended function rewriting
    EXTF
  };
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
   * The argument pt determines which arguments are relevant for purification.
   * For core calculus (CORE_EQ) rules, examples of relevant positions are
   * non-concatenation terms in positions like:
   *   (= * (str.++ * (str.++ * *) * *))
   *   (not (= (str.++ * *) *))
   * For extended function simplification, examples of relevant positions are:
   *   (= (str.replace * * *) "")
   *   (str.contains * *)
   * If we are purifying a substitution with equality, the LHS is a relevant
   * position to purify, and the RHS is treated like CORE_EQ.
   *
   * For example, given substitution (= t ""), an example
   * inference in the core calculus is:
   *   (= (str.++ t "A") (str.++ "B" u)) => false
   * An example of an extended function inference is:
   *   (= (str.replace (str.substr t 0 2) t "C") (str.++ "C" f[t]))
   * Note for the latter, we do not apply the substitution to
   * (str.substr t 0 2).
   *
   * @param pt Determines the positions that are relevant for purification.
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
  static bool purifyCoreSubstitutionAndTarget(PurifyType pt,
                                              Node& tgt,
                                              std::vector<Node>& children,
                                              TheoryProofStepBuffer& psb,
                                              bool concludeTgtNew = false);
  /**
   * Same as above, without a target. This updates termsToPurify with the
   * set of LHS of the substitutions, which are terms that must be purified
   * when applying the resulting substitution to a target.
   */
  static bool purifyCoreSubstitution(std::vector<Node>& children,
                                     TheoryProofStepBuffer& psb,
                                     std::unordered_set<Node>& termsToPurify);
  /**
   * Return the purified form of the predicate lit with respect to a set of
   * terms to purify, call the returned literal lit'.
   * If concludeNew is true, then we add a proof of lit' from lit in psb;
   * otherwise we add a proof of lit from lit'. The positions which are purified
   * are configurable based on the argument pt.
   */
  static Node purifyPredicate(PurifyType pt,
                              Node lit,
                              bool concludeNew,
                              TheoryProofStepBuffer& psb,
                              std::unordered_set<Node>& termsToPurify);
  /**
   * Purify term with respect to a set of terms to purify. This replaces
   * all terms to purify with their purification variables that occur in
   * positions that are relevant for the core calculus of strings (direct
   * children of concat or equal).
   */
  static Node purifyCoreTerm(Node n, std::unordered_set<Node>& termsToPurify);
  /**
   * Purify application, which replaces each direct child nc of n with
   * maybePurifyTerm(nc, termsToPurify).
   */
  static Node purifyApp(Node n, std::unordered_set<Node>& termsToPurify);
  /**
   * Maybe purify term, which returns the skolem variable for n if it occurs
   * in termsToPurify.
   */
  static Node maybePurifyTerm(Node n, std::unordered_set<Node>& termsToPurify);
  /** The lazy fact map */
  NodeInferInfoMap d_lazyFactMap;
  /** Reference to the statistics for the theory of strings/sequences. */
  SequencesStatistics& d_statistics;
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__INFER_PROOF_CONS_H */
