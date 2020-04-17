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
 * TODO: this class should inherit from OutputChannel, not contain it.
 *
 * A layer on top of an output channel to ensure proofs are constructed and
 * available for conflicts and lemmas that may require proofs. It is
 * intended to be owned by TheoryEngine and passed as reference to each of
 * its Theory solvers. Its use can be summarized in two parts:
 *
 * (1) Theory objects should use the output calls to methods in this class,
 * e.g. conflict(...), lemma(...).
 *
 * (2) TheoryEngine should use the methods to get proofs in this class, e.g
 * getProofForConflict(...), getProofForLemma(...) corresponding to the above
 * calls.
 *
 * It is implemented by requiring that calls to conflict(...) provide an
 * pointer to a proof generator object, as part of the TrustNode pair.
 *
 * In more detail, when a call to
 *   ProofOutputChannel::conflict(TrustNode(conf, pfg))
 * is made, this class is required, in the remainder of the current user
 * context, to provide a proof for lem via the call:
 *   ProofOutputChannel::getProofForConflict(conf)
 * This is implemented by calling the getProofForConflict(conf) method of the
 * provided proof generator pfg. Simliar contracts exist for the other calls.
 * Thus, the user of this class needs to ensure that the provided pfg can
 * produce a proof for conf in the remainder of the user context.
 */
class ProofOutputChannel
{
  typedef context::CDHashMap<Node, ProofGenerator*, NodeHashFunction>
      NodeProofGenMap;

 public:
  ProofOutputChannel(OutputChannel& out, context::UserContext* u);
  ~ProofOutputChannel() {}
  /**
   * Let pconf be the pair (Node conf, ProofGenerator * pfg). This method
   * sends conf on the output channel of this class whose proof can be generated
   * by the generator pfg. Apart from pfg, the interface for this method is
   * the same as OutputChannel.
   */
  void trustedConflict(TrustNode pconf);
  /**
   * Get the proof for conflict conf. This method can be called if
   * conflict(TrustNode(conf, pfg)) has been called in this user context. This
   * method returns the proof of conf, according to pfg, or nullptr if we fail
   * to generate a proof. The latter can happen if pfg was nullptr, or if its
   * getProof method failed, indicating an internal failure.
   */
  std::shared_ptr<ProofNode> getProofForConflict(Node conf) const;
  /**
   * Let plem be the pair (Node lem, ProofGenerator * pfg).
   * Send lem on the output channel of this class whose proof can be generated
   * by the generator pfg. Apart from pfg, the interface for this method is
   * the same as OutputChannel.
   */
  LemmaStatus trustedLemma(TrustNode lem,
                           bool removable = false,
                           bool preprocess = false,
                           bool sendAtoms = false);
  /**
   * Get the proof for lemma lem. This method can be called if
   * lemma(TrustNode(lem, pfg), ...) has been called in this user context.
   * This method returns the proof of lem, according to pfg, or nullptr if we
   * fail to generate a proof. The latter can happen if pfg was nullptr, or if
   * its getProof method failed, indicating an internal failure.
   */
  std::shared_ptr<ProofNode> getProofForLemma(Node lem) const;

  /** Get the node key for which conflict calls are cached */
  static Node getConflictKeyValue(Node conf);
  /** Get the node key for which lemma calls are cached */
  static Node getLemmaKeyValue(Node lem);
  //---------------- interface to output channel that doesnt require proofs
  /** require phase */
  void requirePhase(TNode n, bool phase);
  /** set incomplete */
  void setIncomplete();
  //---------------- end interface to output channel that doesnt require proofs
 private:
  /** Get proof generator for key, or nullptr if it does not exist */
  ProofGenerator* getProofGeneratorForKey(Node key) const;
  /** Reference to an output channel */
  OutputChannel& d_out;
  /**
   * A user-context-dependent map from lemmas and conflicts to proof generators
   */
  NodeProofGenMap d_outPfGen;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__PROOF_OUTPUT_CHANNEL_H */
