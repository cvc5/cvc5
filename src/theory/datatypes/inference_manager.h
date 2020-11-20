/*********************                                                        */
/*! \file inference_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Datatypes inference manager
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__DATATYPES__INFERENCE_MANAGER_H
#define CVC4__THEORY__DATATYPES__INFERENCE_MANAGER_H

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "theory/datatypes/infer_proof_cons.h"
#include "theory/datatypes/inference.h"
#include "theory/inference_manager_buffered.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace datatypes {

/**
 * The datatypes inference manager, which uses the above class for
 * inferences.
 */
class InferenceManager : public InferenceManagerBuffered
{
  friend class DatatypesInference;

 public:
  InferenceManager(Theory& t, TheoryState& state, ProofNodeManager* pnm);
  ~InferenceManager();
  /**
   * Add pending inference, which may be processed as either a fact or
   * a lemma based on mustCommunicateFact in DatatypesInference above.
   *
   * @param conc The conclusion of the inference
   * @param exp The explanation of the inference
   * @param forceLemma Whether this inference *must* be processed as a lemma.
   * Otherwise, it may be processed as a fact or lemma based on
   * mustCommunicateFact.
   * @param i The inference, used for stats and as a hint for constructing
   * the proof of (conc => exp)
   */
  void addPendingInference(Node conc,
                           Node exp,
                           bool forceLemma = false,
                           InferId i = InferId::NONE);
  /**
   * Process the current lemmas and facts. This is a custom method that can
   * be seen as overriding the behavior of calling both doPendingLemmas and
   * doPendingFacts. It determines whether facts should be sent as lemmas
   * or processed internally.
   */
  void process();
  /**
   * Send lemma immediately on the output channel
   */
  void sendDtLemma(Node lem,
                   InferId i = InferId::NONE,
                   LemmaProperty p = LemmaProperty::NONE,
                   bool doCache = true);
  /**
   * Send conflict immediately on the output channel
   */
  void sendDtConflict(const std::vector<Node>& conf, InferId i = InferId::NONE);
  /**
   * Send lemmas with property NONE on the output channel immediately.
   * Returns true if any lemma was sent.
   */
  bool sendLemmas(const std::vector<Node>& lemmas);

 private:
  /** Are proofs enabled? */
  bool isProofEnabled() const;
  /**
   * Process datatype inference as a lemma
   */
  bool processDtLemma(Node conc,
                      Node exp,
                      InferId id,
                      LemmaProperty p = LemmaProperty::NONE,
                      bool doCache = true);
  /**
   * Process datatype inference as a fact
   */
  bool processDtFact(Node conc, Node exp, InferId id);
  /**
   * Helper function for the above methods. Returns the conclusion, which
   * may be modified so that it is compatible with proofs. If proofs are
   * enabled, it ensures the proof constructor is ready to provide a proof
   * of (=> exp conc).
   *
   * In particular, if conc is a Boolean equality, it is rewritten. This is
   * to ensure that we do not assert equalities of the form (= t true)
   * or (= t false) to the equality engine, which have a reserved internal
   * status for proof generation. If this is not done, then it is possible
   * to have proofs with missing connections and hence free assumptions.
   */
  Node prepareDtInference(Node conc, Node exp, InferId id, InferProofCons* ipc);
  /** The false node */
  Node d_false;
  /**
   * Counts the number of applications of each type of inference processed by
   * the above method as facts, lemmas and conflicts.
   */
  HistogramStat<InferId> d_inferenceLemmas;
  HistogramStat<InferId> d_inferenceFacts;
  HistogramStat<InferId> d_inferenceConflicts;
  /** Pointer to the proof node manager */
  ProofNodeManager* d_pnm;
  /** The inference to proof converter */
  std::unique_ptr<InferProofCons> d_ipc;
  /** An eager proof generator for lemmas */
  std::unique_ptr<EagerProofGenerator> d_lemPg;
};

}  // namespace datatypes
}  // namespace theory
}  // namespace CVC4

#endif
