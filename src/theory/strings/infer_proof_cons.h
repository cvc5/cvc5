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
#include "expr/proof_checker.h"
#include "expr/proof_rule.h"
#include "theory/builtin/proof_checker.h"
#include "theory/strings/infer_info.h"
#include "theory/strings/sequences_stats.h"
#include "theory/theory_proof_step_buffer.h"
#include "theory/uf/proof_equality_engine.h"

namespace CVC4 {
namespace theory {
namespace strings {

/**
 * Converts between the strings-specific (untrustworthy) InferInfo class and
 * information about how to construct a trustworthy proof step, e.g.
 * (PfRule, children, args).
 *
 * It also may act as a (lazy) proof generator.
 */
class InferProofCons : public ProofGenerator
{
  typedef context::CDHashMap<Node, std::shared_ptr<InferInfo>, NodeHashFunction>
      NodeInferInfoMap;

 public:
  InferProofCons(context::Context* c,
                 ProofNodeManager* pnm,
                 SequencesStatistics& statistics,
                 bool pfEnabled);
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
  /** convert
   *
   * This method is called when the theory of strings makes an inference
   * described by an inference info ii, which is of the form:
   * (<conclusion>, <Inference_id>, <antecendant>).
   *
   * This method converts this call to instructions on what the proof rule
   * step(s) are for concluding the conclusion of the inference. This
   * information is stored in the argument ps, which consists of:
   * (1) A proof rule identifier (d_rule).
   * (2) The premises of the proof step (d_children).
   * (3) Arguments to the proof step (d_args).
   *
   * NOTE: if the proof for the inference cannot be captured by a single
   * step, then the d_rule field of ps is not set, and useBuffer is set to
   * true. In this case, the ProofStepBuffer of this class contains (multiple)
   * steps for how to construct a proof for the inference. This buffer can be
   * obtained by getBuffer() below.
   *
   * This method returns the conclusion of ii.
   */
  Node convert(const InferInfo& ii, ProofStep& ps, bool& useBuffer);
  /**
   * Internal version of above, where the fields of ii have been expanded
   * into separate arguments.
   */
  Node convert(Inference infer,
               bool isRev,
               Node conc,
               const std::vector<Node>& exp,
               ProofStep& ps,
               bool& useBuffer);
  /** Get the proof step buffer */
  ProofStepBuffer* getBuffer();

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
  /**
   * Convert length proof. If this method returns true, it adds proof step(s)
   * to the buffer that conclude lenReq from premises lenExp.
   */
  bool convertLengthPf(Node lenReq, const std::vector<Node>& lenExp);
  /**
   */
  Node convertTrans(Node eqa, Node eqb);
  /** the proof node manager */
  ProofNodeManager* d_pnm;
  /** The lazy fact map */
  NodeInferInfoMap d_lazyFactMap;
  /** The proof step buffer */
  TheoryProofStepBuffer d_psb;
  /** Reference to the statistics for the theory of strings/sequences. */
  SequencesStatistics& d_statistics;
  /** Whether proofs are enabled */
  bool d_pfEnabled;
};

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__INFER_PROOF_CONS_H */
