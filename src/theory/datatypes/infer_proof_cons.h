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
 * Inference to proof conversion for datatypes.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__DATATYPES__INFER_PROOF_CONS_H
#define CVC5__THEORY__DATATYPES__INFER_PROOF_CONS_H

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "proof/proof_generator.h"
#include "smt/env_obj.h"
#include "theory/datatypes/inference.h"

namespace cvc5::internal {
namespace theory {
namespace datatypes {

/**
 * Converts between the datatype-specific (untrustworthy) DatatypesInference
 * class and information about how to construct a trustworthy proof step
 * (PfRule, children, args). It acts as a (lazy) proof generator where the
 * former is registered via notifyFact and the latter is asked for in
 * getProofFor, typically by the proof equality engine.
 *
 * The main (private) method of this class is convert below, which is
 * called when we need to construct a proof node from an InferInfo.
 */
class InferProofCons : protected EnvObj, public ProofGenerator
{
  typedef context::CDHashMap<Node, std::shared_ptr<DatatypesInference>>
      NodeDatatypesInferenceMap;

 public:
  InferProofCons(Env& env, context::Context* c);
  ~InferProofCons() {}
  /**
   * This is called to notify that di is an inference that may need a proof
   * in the future.
   *
   * In detail, this class should be prepared to respond to a call to:
   *   getProofFor(di.d_conc)
   * in the remainder of the SAT context. This method copies di and stores it
   * in the context-dependent map d_lazyFactMap below.
   *
   * This is used for lazy proof construction, where proofs are constructed
   * only for facts that are explained.
   */
  void notifyFact(const std::shared_ptr<DatatypesInference>& di);

  /**
   * This returns the proof for fact. This is required for using this class as
   * a lazy proof generator.
   *
   * It should be the case that a call was made to notifyFact(di) where
   * di.d_conc is fact in this SAT context.
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
   * information is stored in cdp.
   */
  void convert(InferenceId infer, TNode conc, TNode exp, CDProof* cdp);
  /** A dummy context used by this class if none is provided */
  context::Context d_context;
  /** The lazy fact map */
  NodeDatatypesInferenceMap d_lazyFactMap;
};

}  // namespace datatypes
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__DATATYPES__INFER_PROOF_CONS_H */
