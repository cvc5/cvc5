/*********************                                                        */
/*! \file proof_output_channel.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The proof output channel class
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__PROOF_OUTPUT_CHANNEL_H
#define CVC4__THEORY__PROOF_OUTPUT_CHANNEL_H

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "expr/proof_node.h"
#include "theory/output_channel.h"
#include "theory/proof_generator.h"

namespace CVC4 {
namespace theory {

/**
 * A layer on top of an output channel to ensure proofs are constructed and
 * available for conflicts and lemmas that may require proofs.
 * 
 * When a call to
 *   OutputChannel::lemma(lem, .. ) 
 * is made by a Theory, it is required, in the remainder of the current user
 * context, to provide a proof for lem via the call:
 *   Theory::getProof(ProofOutputChannel::getLemmaKeyValue(lem))
 * Simliar contracts exist for the other calls on OutputChannel.
 * 
 * The purpose of the ProofOutputChannel is to ensure that the above contracts
 * are met. In particular, for each conflict or lemma sent on the output
 * channel of this class, we must provide a ProofGenerator object (an instance
 * of the abstract class), which can provide a proof for that lemma. Notice
 * that different proof generators can be provided for different lemmas for
 * the same Theory object.
 */
class ProofOutputChannel
{
  typedef context::CDHashMap<Node, ProofGenerator*, NodeHashFunction>
      NodeProofGenMap;

 public:
  ProofOutputChannel(OutputChannel& out, context::UserContext* u);
  ~ProofOutputChannel() {}
  /**
   * Send conf on the output channel of this class whose proof can be generated
   * by the generator pfg. Apart from pfg, the interface for this method is
   * the same as OutputChannel.
   */
  void conflict(Node conf, ProofGenerator* pfg);
  /**
   * Send lem on the output channel of this class whose proof can be generated
   * by the generator pfg. Apart from pfg, the interface for this method is
   * the same as OutputChannel.
   */
  LemmaStatus lemma(Node lem,
                    ProofGenerator* pfg,
                    bool removable = false,
                    bool preprocess = false,
                    bool sendAtoms = false);

  /**
   * Get proof for formula n. This returns the corresponding proof for formula
   * n, where n is either:
   * (1) getConflictKeyValue(conf) for some conf passed to conflict(conf,...)
   * (2) getLemmaKeyValue(lem) for some lem passed to lemma(lem, ...)
   * 
   * This calls the appropriate proof generator that was provided to
   * generate and return the corresponding proof. If not is found, the nullptr
   * is returned and an assertion is thrown.
   */
  std::shared_ptr<ProofNode> getProof(Node n) const;
  /** Get the node key for which conflict calls are cached */
  static Node getConflictKeyValue(Node conf);
  /** Get the node key for which lemma calls are cached */
  static Node getLemmaKeyValue(Node lem);
 private:
  /** Reference to an output channel */
  OutputChannel& d_out;
  /**
   * A user-context-dependent map from lemmas and conflicts to proof generators
   */
  NodeProofGenMap d_lemPfGen;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__PROOF_OUTPUT_CHANNEL_H */
