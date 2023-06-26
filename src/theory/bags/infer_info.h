/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Aina Niemetz
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

#ifndef CVC5__THEORY__BAGS__INFER_INFO_H
#define CVC5__THEORY__BAGS__INFER_INFO_H

#include <map>
#include <vector>

#include "expr/node.h"
#include "theory/inference_id.h"
#include "theory/theory_inference.h"

namespace cvc5::internal {
namespace theory {

class InferenceManagerBuffered;

namespace bags {

/**
 * An inference. This is a class to track an unprocessed call to either
 * send a fact, lemma, or conflict that is waiting to be asserted to the
 * equality engine or sent on the output channel.
 */
class InferInfo : public TheoryInference
{
 public:
  InferInfo(InferenceManagerBuffered* im, InferenceId id);
  ~InferInfo() {}
  /** Process lemma */
  TrustNode processLemma(LemmaProperty& p) override;
  /** Pointer to the class used for processing this info */
  InferenceManagerBuffered* d_im;
  /** The conclusion */
  Node d_conclusion;
  /**
   * The premise(s) of the inference, interpreted conjunctively. These are
   * literals that currently hold in the equality engine.
   */
  std::vector<Node> d_premises;

  /**
   * A map of nodes to their skolem variables introduced as a result of this
   * inference.
   */
  std::map<Node, Node> d_skolems;
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
  /**
   * @return the lemma for this InferInfo.
   */
  Node getLemma() const;
};

/**
 * Writes an inference info to a stream.
 *
 * @param out The stream to write to
 * @param ii The inference info to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, const InferInfo& ii);

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BAGS__INFER_INFO_H */
