/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mudathir Mohamed, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Inference information utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__INFER_INFO_H
#define CVC5__THEORY__STRINGS__INFER_INFO_H

#include <map>
#include <vector>

#include "expr/node.h"
#include "theory/inference_id.h"
#include "theory/theory_inference.h"
#include "util/safe_print.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

/**
 * Length status, used for indicating the length constraints for Skolems
 * introduced by the theory of strings.
 */
enum LengthStatus
{
  // The length of the Skolem should not be constrained. This should be
  // used for Skolems whose length is already implied.
  LENGTH_IGNORE,
  // The length of the Skolem is not specified, and should be split on.
  LENGTH_SPLIT,
  // The length of the Skolem is exactly one.
  LENGTH_ONE,
  // The length of the Skolem is greater than or equal to one.
  LENGTH_GEQ_ONE
};

class InferenceManager;

/**
 * An inference. This is a class to track an unprocessed call to either
 * send a fact, lemma, or conflict that is waiting to be asserted to the
 * equality engine or sent on the output channel.
 *
 * For the sake of proofs, the premises in InferInfo have a particular
 * ordering for many of the core strings rules, which is expected by
 * InferProofCons for constructing proofs of F_CONST, F_UNIFY, N_CONST, etc.
 * which apply to a pair of string terms t and s. At a high level, the ordering
 * expected in d_ant is:
 * (1) (multiple) literals that explain why t and s have the same prefix/suffix,
 * (2) t = s,
 * (3) (optionally) a length constraint.
 * For example, say we have:
 *   { x ++ y ++ v1 = z ++ w ++ v2, x = z ++ u, u = "", len(y) = len(w) }
 * We can conclude y = w by the N_UNIFY rule from the left side. The premise
 * has the following form:
 * - (prefix up to y/w equal) x = z ++ u, u = "",
 * - (main equality) x ++ y ++ v1 = z ++ w ++ v2,
 * - (length constraint) len(y) = len(w).
 */
class InferInfo : public TheoryInference
{
 public:
  InferInfo(InferenceId id);
  ~InferInfo() {}
  /** Process lemma */
  TrustNode processLemma(LemmaProperty& p) override;
  /** Process internal fact */
  Node processFact(std::vector<Node>& exp, ProofGenerator*& pg) override;
  /** Pointer to the class used for processing this info */
  InferenceManager* d_sim;
  /** Whether it is the reverse form of the above id */
  bool d_idRev;
  /** The conclusion */
  Node d_conc;
  /**
   * The premise(s) of the inference, interpreted conjunctively. These are
   * literals that currently hold in the equality engine.
   */
  std::vector<Node> d_premises;
  /**
   * The "new literal" premise(s) of the inference, interpreted
   * conjunctively. These are literals that were needed to show the conclusion
   * but do not currently hold in the equality engine. These should be a subset
   * of d_ant. In other words, premises that are not explained are stored
   * in *both* d_ant and d_noExplain.
   */
  std::vector<Node> d_noExplain;
  /**
   * A list of new skolems introduced as a result of this inference. They
   * are mapped to by a length status, indicating the length constraint that
   * can be assumed for them.
   */
  std::map<LengthStatus, std::vector<Node> > d_skolems;
  /**
   * The pending phase requirements, see InferenceManager::sendPhaseRequirement.
   */
  std::map<Node, bool> d_pendingPhase;
  /**
   * The normal form pair that is cached as a result of this inference.
   */
  Node d_nfPair[2];
  /**  Is this infer info trivial? True if d_conc is true. */
  bool isTrivial() const;
  /**
   * Does this infer info correspond to a conflict? True if d_conc is false
   * and it has no new premises (d_noExplain).
   */
  bool isConflict() const;
  /**
   * Does this infer info correspond to a "fact". A fact is an inference whose
   * conclusion should be added as an equality or predicate to the equality
   * engine with no new external premises (d_noExplain).
   */
  bool isFact() const;
  /** Get premises */
  Node getPremises() const;
};

/**
 * Writes an inference info to a stream.
 *
 * @param out The stream to write to
 * @param ii The inference info to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, const InferInfo& ii);

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__INFER_INFO_H */
