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
#include "expr/proof_step_buffer.h"
#include "theory/strings/infer_info.h"
#include "theory/strings/sequences_stats.h"
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
                 ProofChecker* pc,
                 SequencesStatistics& statistics,
                 bool pfEnabled);
  ~InferProofCons() {}
  /** notify fact */
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
   * This adds the proof steps for fact to proof pf with the given overwrite
   * policy. This is required for using this class as a lazy proof generator.
   * 
   * It should be the case that a call was made to convert(...), where conc
   * was fact, in the current SAT context.
   */
  bool addProofTo(Node fact, CDProof* pf, bool forceOverwrite = false) override;
  /** Identify this generator (for debugging, etc..) */
  virtual std::string identify() const override;

 private:
  /** 
   * Convert length proof. If this method returns true, it adds proof step(s)
   * to the buffer that conclude lenReq from premises lenExp.
   */
  bool convertLengthPf(Node lenReq, const std::vector<Node>& lenExp);
  /** 
   * Apply macro transform. If this method returns true, it adds proof step(s)
   * to the buffer that conclude tgt from premises tgt, exp. In particular,
   * it may attempt to apply MACRO_SR_PRED_TRANSFORM. This method should be
   * applied when src and tgt are equivalent formulas assuming exp. 
   */
  bool convertPredTransform(Node src, Node tgt, const std::vector<Node>& exp);
  /** The lazy fact map */
  NodeInferInfoMap d_lazyFactMap;
  /** The proof step buffer */
  ProofStepBuffer d_psb;
  /** Reference to the statistics for the theory of strings/sequences. */
  SequencesStatistics& d_statistics;
  /** Whether proofs are enabled */
  bool d_pfEnabled;
};

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__INFER_PROOF_CONS_H */
