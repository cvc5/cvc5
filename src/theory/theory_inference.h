/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The theory inference utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__THEORY_INFERENCE_H
#define CVC5__THEORY__THEORY_INFERENCE_H

#include "expr/node.h"
#include "theory/inference_id.h"
#include "theory/output_channel.h"

namespace cvc5::internal {
namespace theory {

class TheoryInferenceManager;

/**
 * A theory inference base class. This class is an abstract data structure for
 * storing pending lemmas or facts in the buffered inference manager. It can
 * be seen a single use object capturing instructions for making a single
 * call to TheoryInferenceManager for lemmas or facts.
 */
class TheoryInference
{
 public:
  TheoryInference(InferenceId id) : d_id(id) {}
  virtual ~TheoryInference() {}

  /**
   * Process lemma, return the trust node to pass to
   * TheoryInferenceManager::trustedLemma. In addition, the inference should
   * process any internal side effects of the lemma.
   *
   * @param p The property of the lemma which will be passed to trustedLemma
   * for this inference. If this call does not update p, the default value will
   * be used.
   * @return The trust node (of kind TrustNodeKind::LEMMA) corresponding to the
   * lemma and its proof generator.
   */
  virtual TrustNode processLemma(LemmaProperty& p) { return TrustNode::null(); }
  /**
   * Process internal fact, return the conclusion to pass to
   * TheoryInferenceManager::assertInternalFact. In addition, the inference
   * should process any internal side effects of the fact.
   *
   * @param exp The explanation for the returned conclusion. Each node added to
   * exp should be a (conjunction of) literals that hold in the current equality
   * engine.
   * @return The (possibly negated) conclusion.
   */
  virtual Node processFact(std::vector<Node>& exp, ProofGenerator*& pg)
  {
    return Node::null();
  }

  /** Get the InferenceId of this theory inference. */
  InferenceId getId() const { return d_id; }
  /** Set the InferenceId of this theory inference. */
  void setId(InferenceId id) { d_id = id; }

 private:
  InferenceId d_id;
};

/**
 * A simple theory lemma with no side effects. Makes a single call to
 * trustedLemma in its process method.
 */
class SimpleTheoryLemma : public TheoryInference
{
 public:
  SimpleTheoryLemma(InferenceId id, Node n, LemmaProperty p, ProofGenerator* pg);
  virtual ~SimpleTheoryLemma() {}
  /** Process lemma */
  TrustNode processLemma(LemmaProperty& p) override;
  /** The lemma to send */
  Node d_node;
  /** The lemma property (see OutputChannel::lemma) */
  LemmaProperty d_property;
  /**
   * The proof generator for this lemma, which if non-null, is wrapped in a
   * TrustNode to be set on the output channel via trustedLemma at the time
   * the lemma is sent. This proof generator must be able to provide a proof
   * for d_node in the remainder of the user context.
   */
  ProofGenerator* d_pg;
};

/**
 * A simple internal fact with no side effects. Makes a single call to
 * assertInternalFact in its process method.
 */
class SimpleTheoryInternalFact : public TheoryInference
{
 public:
  SimpleTheoryInternalFact(InferenceId id, Node conc, Node exp, ProofGenerator* pg);
  virtual ~SimpleTheoryInternalFact() {}
  /** Process internal fact */
  Node processFact(std::vector<Node>& exp, ProofGenerator*& pg) override;
  /** The lemma to send */
  Node d_conc;
  /** The explanation */
  Node d_exp;
  /** The proof generator */
  ProofGenerator* d_pg;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif
