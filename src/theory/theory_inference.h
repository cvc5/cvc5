/*********************                                                        */
/*! \file theory_inference.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The theory inference utility
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__THEORY_INFERENCE_H
#define CVC4__THEORY__THEORY_INFERENCE_H

#include "expr/node.h"
#include "theory/output_channel.h"

namespace CVC4 {
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
  virtual ~TheoryInference() {}
  /**
   * Called by the provided inference manager to process this inference. This
   * method should make call(s) to inference manager to process this
   * inference, as well as processing any specific side effects. This method
   * typically makes a single call to the provided inference manager e.g.
   * d_im->trustedLemma or d_im->assertFactInternal. Notice it is the sole
   * responsibility of this class to make this call; the inference manager
   * does not call itself otherwise when processing pending inferences.
   *
   * @return true if the inference was successfully processed by the inference
   * manager. This method for instance returns false if it corresponds to a
   * lemma that was already cached by im and hence was discarded.
   */
  virtual bool process(TheoryInferenceManager* im) = 0;
};

/**
 * A simple theory lemma with no side effects. Makes a single call to
 * trustedLemma in its process method.
 */
class SimpleTheoryLemma : public TheoryInference
{
 public:
  SimpleTheoryLemma(Node n, LemmaProperty p, ProofGenerator* pg);
  virtual ~SimpleTheoryLemma() {}
  /**
   * Send the lemma using inference manager im, return true if the lemma was
   * sent.
   */
  virtual bool process(TheoryInferenceManager* im) override;
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
 * assertFactInternal in its process method.
 */
class SimpleTheoryInternalFact : public TheoryInference
{
 public:
  SimpleTheoryInternalFact(Node conc, Node exp, ProofGenerator* pg);
  virtual ~SimpleTheoryInternalFact() {}
  /**
   * Send the lemma using inference manager im, return true if the lemma was
   * sent.
   */
  virtual bool process(TheoryInferenceManager* im) override;
  /** The lemma to send */
  Node d_conc;
  /** The explanation */
  Node d_exp;
  /** The proof generator */
  ProofGenerator* d_pg;
};

}  // namespace theory
}  // namespace CVC4

#endif
