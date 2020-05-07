/*********************                                                        */
/*! \file proof_engine_output_channel.h
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

#ifndef CVC4__THEORY__PROOF_ENGINE_OUTPUT_CHANNEL_H
#define CVC4__THEORY__PROOF_ENGINE_OUTPUT_CHANNEL_H

#include "context/cdhashmap.h"
#include "expr/lazy_proof.h"
#include "expr/node.h"
#include "expr/proof_node.h"
#include "theory/eager_proof_generator.h"
#include "theory/engine_output_channel.h"

namespace CVC4 {
namespace theory {

/**
 * TODO: merge with engine output channel
 *
 * A layer on top of an output channel to ensure proofs are constructed and
 * available for conflicts and lemmas that may require proofs. It is
 * intended to be owned by TheoryEngine and passed as reference to each of
 * its Theory solvers. Its use can be summarized in two parts:
 *
 * (1) Theory objects should use the output calls to methods in this class,
 * e.g. trustedConflict(...), trustedLemma(...).
 *
 * (2) This class is responsible for adding proof steps to the provide proof
 * object that correspond to steps.
 *
 * It is implemented by requiring that calls to conflict(...) provide an
 * pointer to a proof generator object, as part of the TrustNode pair.
 *
 * In more detail, when a call to
 *   ProofOutputChannel::trustedConflict(TrustNode(conf, pfg))
 * is made
 */
class ProofEngineOutputChannel : public EngineOutputChannel
{
  typedef context::CDHashMap<Node, ProofGenerator*, NodeHashFunction>
      NodeProofGenMap;

 public:
  ProofEngineOutputChannel(TheoryEngine* engine,
                           theory::TheoryId theory,
                           LazyCDProof* lpf);
  ~ProofEngineOutputChannel() {}
  /**
   * Let pconf be the pair (Node conf, ProofGenerator * pfg). This method
   * sends conf on the output channel of this class whose proof can be generated
   * by the generator pfg. It stores the mapping
   *   getConflictKeyValue(conf) |-> pfg
   * as a (lazy) step in the lazy proof object owned by this class.
   */
  void trustedConflict(TrustNode pconf) override;
  /**
   * Let plem be the pair (Node lem, ProofGenerator * pfg).
   * Send lem on the output channel of this class whose proof can be generated
   * by the generator pfg. Apart from pfg, the interface for this method is
   * the same as OutputChannel. It stores the mapping
   *   getLemmaKeyValue(lem) |-> pfg
   * as a (lazy) step in the lazy proof object owned by this class.
   */
  LemmaStatus trustedLemma(TrustNode plem,
                           bool removable = false,
                           bool preprocess = false,
                           bool sendAtoms = false) override;

  /** Get the node key for which conflict calls are cached */
  static Node getConflictKeyValue(Node conf);
  /** Get the node key for which lemma calls are cached */
  static Node getLemmaKeyValue(Node lem);

 private:
  /** Pointer to the lazy proof
   *
   * This object stores the mapping between formulas (conflicts or lemmas)
   * and the proof generator provided for them.
   */
  LazyCDProof* d_lazyPf;
  /** 
   * Add coarse grained THEORY_LEMMA step for formula f that is the key of
   * a lemma or conflict being sent out on the output channel of this class.
   */
  bool addTheoryLemmaStep(Node f);
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__PROOF_OUTPUT_CHANNEL_H */
