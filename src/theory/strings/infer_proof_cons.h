/*********************                                                        */
/*! \file infer_proof_cons.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Inference to proof conversion
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__INFER_PROOF_CONS_H
#define CVC4__THEORY__STRINGS__INFER_PROOF_CONS_H

#include <vector>

#include "expr/node.h"
#include "expr/proof_rule.h"
#include "theory/strings/infer_info.h"
#include "theory/uf/proof_equality_engine.h"
#include "theory/strings/sequences_stats.h"

namespace CVC4 {
namespace theory {
namespace strings {

/**
 * Converts between Inference and information needed to provide a proof step
 * (PfRule, children, args).
 */
class InferProofCons
{
 public:
  InferProofCons(eq::ProofEqEngine& pfee,
                 SequencesStatistics& statistics, bool pfEnabled = false);
  ~InferProofCons() {}
  /** convert
   *
   * This method is called when the theory of strings makes an inference
   * described by an inference info ii, which is of the form:
   * (<conclusion>, <Inference_id>, <antecendant> <new-antecedant>).
   *
   * This method converts this call to a proof step consisting of
   * (1) A returned proof rule identifier.
   * (2) The premises of the proof step (pfChildren).
   * (3) The subset of pfChildren which should be "explained". Notice this is
   * only relevant if ii corresponds to a lemma.
   * (4) Arguments to the proof step (pfArgs).
   */
  PfRule convert(const InferInfo& ii,
                 std::vector<Node>& pfChildren,
                 std::vector<Node>& pfExp,
                 std::vector<Node>& pfArgs);
  PfRule convert(Inference infer,
                 Node conc,
                 const std::vector<Node>& exp,
                 const std::vector<Node>& expn,
                 std::vector<Node>& pfChildren,
                 std::vector<Node>& pfExp,
                 std::vector<Node>& pfArgs);

 private:
  /** The proof-producing equality engine, used for intermediate assertions */
  eq::ProofEqEngine& d_pfee;
  /** Reference to the statistics for the theory of strings/sequences. */
  SequencesStatistics& d_statistics;
  /** Whether proofs are enabled */
  bool d_pfEnabled;
};

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__INFER_PROOF_CONS_H */
