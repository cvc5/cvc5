/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A utility for converting proof nodes.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__PROOF_NODE_CONVERTER_H
#define CVC5__PROOF__PROOF_NODE_CONVERTER_H

#include <map>
#include <memory>

#include "expr/node.h"
#include "proof/proof_node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

class CDProof;
class ProofNode;
class ProofNodeManager;

/**
 * A virtual callback class for converting ProofNode. An example use case of
 * this class is to transform a proof so that it does not use mixed arithmetic.
 *
 * We convert proofs in a bottom-up manner using an overloaded method convert.
 */
class ProofNodeConverterCallback
{
 public:
  ProofNodeConverterCallback();
  virtual ~ProofNodeConverterCallback();
  /**
   * Should proof pn be converted?
   *
   * Proofs are converted in a bottom-up manner (i.e. at post-traversal).
   * This method is used as an optimization to see if the proof node requires
   * any conversion. This method is called on proof nodes whose premises were
   * *not* modified already by this converter. We always call convert for proof
   * nodes whose premises were modified.
   *
   * @param pn the proof node that maybe should be converted
   * @return whether we should run the convert method on pn
   */
  virtual bool shouldConvert(std::shared_ptr<ProofNode> pn);
  /**
   * Convert the proof rule application, store steps in cdp. Return a non-null
   * formula if successful, which should be given a closed proof in cdp. It can
   * be assumed that cdp contains proofs of each fact in children.
   *
   * @param res The original conclusion of the proof node,
   * @param id The original id of the proof node,
   * @param children The *converted* conclusions of the children of the proof
   * node. Note these may have different conclusions than they had in the
   * original proof.
   * @param arg The original arguments of the proof node,
   * @param cdp The proof to add to
   * @return a fomula F such that cdp has a closed proof of F, or null if we
   * fail to convert.
   */
  virtual Node convert(Node res,
                       ProofRule id,
                       const std::vector<Node>& children,
                       const std::vector<Node>& args,
                       CDProof* cdp) = 0;
};

/**
 * A generic class for converting ProofNode. It is parameterized by a callback
 * class. Its process method runs this callback on all subproofs of a provided
 * ProofNode application and reconstructs a proof based on the results of the
 * callback. This class uses local CDProof objects that should be filled in the
 * callback for each ProofNode to create for the conversion. This update
 * process is applied in a *post-order* traversal, where the converted children
 * are provided to the callback. It returns nullptr if the conversion failed,
 * i.e. if the callback returned Node::null() for any proof step.
 */
class ProofNodeConverter : protected EnvObj
{
 public:
  /**
   * @param env Reference to the environment
   * @param cb The callback to apply to each node
   * @param autoSym Whether intermediate CDProof objects passed to updater
   * callbacks automatically introduce SYMM steps.
   */
  ProofNodeConverter(Env& env,
                     ProofNodeConverterCallback& cb,
                     bool autoSym = true);
  /**
   * Process, which performs the main conversion technique described
   * above.
   */
  std::shared_ptr<ProofNode> process(std::shared_ptr<ProofNode> pf);

 private:
  /** The callback */
  ProofNodeConverterCallback& d_cb;
  /**
   * Helper method for process.
   *
   * @param pf The proof to process
   * @param pchildren The converted children of pf, which may have different
   * conclusions from the children of pf.
   */
  std::shared_ptr<ProofNode> processInternal(
      std::shared_ptr<ProofNode> pf,
      const std::vector<std::shared_ptr<ProofNode>>& pchildren);
};

}  // namespace cvc5::internal

#endif
