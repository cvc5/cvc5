/*********************                                                        */
/*! \file eager_proof_generator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The eager proof generator class
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__EAGER_PROOF_GENERATOR_H
#define CVC4__THEORY__EAGER_PROOF_GENERATOR_H

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "expr/proof_generator.h"
#include "expr/proof_node.h"
#include "theory/trust_node.h"

namespace CVC4 {
namespace theory {

/**
 * An eager proof generator, with explicit proof caching.
 *
 * The intended use of this class is to store proofs for lemmas and conflicts
 * at the time they are sent out on the ProofOutputChannel. This means that the
 * getProofForConflict and getProofForLemma methods are lookups in a
 * (user-context depedent) map, the field d_proofs below.
 *
 * In detail, the method setProofForConflict(conf, pf) should be called prior to
 * calling ProofOutputChannel(TrustNode(conf,X)), where X is this generator.
 * Similarly for setProofForLemma.
 *
 * The intended usage of this class in combination with ProofOutputChannel is
 * the following:
 * //-----------------------------------------------------------
 *   class MyEagerProofGenerator : public EagerProofGenerator
 *   {
 *     public:
 *      TrustNode getProvenConflictByMethodX(...)
 *      {
 *        Node conf = [construct conflict];
 *        std::shared_ptr<ProofNode> pf = [construct the proof for conf];
 *        // call mkTrustNode, which calls setProofForLemma, and constructs
 *        // the trust node
 *        return mkTrustNode(conf,pf);
 *      }
 *   };
 *   // [1] Make objects given user context u and output channel out
 *   MyEagerProofGenerator epg(u);
 *   ProofOutputChannel poc(out, u);
 *
 *   // [2] Assume epg realizes there is a conflict. We have it store the proof
 *   // internally and return the conflict node paired with epg.
 *   TrustNode pconf = epg.getProvenConflictByMethodX(...);
 *
 *   // [3] Send the conflict on the proof output channel, which itself
 *   // references epg.
 *   poc.conflict(pconf);
 *
 *   // [4] Any time later in the user context, we may ask poc for the proof,
 *   // where notice this calls the getProof method of epg.
 *   Node conf = pconf.first;
 *   std::shared_ptr<ProofNode> pf = poc.getProofForConflict(conf);
 * //-----------------------------------------------------------
 * In other words, the proof generator epg is responsible for creating and
 * storing the proof internally, and the proof output channel is responsible for
 * maintaining the map that epg is who to ask for the proof of the conflict.
 */
class EagerProofGenerator : public ProofGenerator
{
  typedef context::CDHashMap<Node, std::shared_ptr<ProofNode>, NodeHashFunction>
      NodeProofNodeMap;

 public:
  EagerProofGenerator(context::Context* c, ProofNodeManager* pnm);
  ~EagerProofGenerator() {}
  /** Get the proof for formula f. */
  std::shared_ptr<ProofNode> getProofFor(Node f) override;
  /** Can we give the proof for formula f? */
  bool hasProofFor(Node f) override;
  /**
   * Make trust node: wrap n in a trust node with this generator, and have it
   * store the proof pf to
   *
   * @param n The proven node,
   * @param pf The proof of n,
   * @param isConflict Whether this is a conflict (otherwise it is a lemma)
   * @return The trust node corresponding to the fact that this generator has
   * a proof of n.
   */
  TrustNode mkTrustNode(Node n,
                        std::shared_ptr<ProofNode> pf,
                        bool isConflict = false);
  /**
   * Make trust node from a single step proof.
   */
  TrustNode mkTrustNode(Node n,
                        PfRule id,
                        const std::vector<Node>& args,
                        bool isConflict = false);
  //--------------------------------------- common proofs
  /**
   * This returns the trust node corresponding to the splitting lemma
   * (or f (not f)) and this generator. The method registers its proof in the
   * map maintained by this class. The return value can safely be passed to
   * ProofOutputChannel::sendLemma.
   */
  TrustNode assertSplit(Node f);
  //--------------------------------------- end common proofs
  /** identify */
  std::string identify() const override { return "EagerProofGenerator"; }

 protected:
  /** Set that pf is the proof for conflict conf */
  void setProofForConflict(Node conf, std::shared_ptr<ProofNode> pf);
  /** Set that pf is the proof for lemma lem */
  void setProofForLemma(Node lem, std::shared_ptr<ProofNode> pf);
  /** Set that pf is the proof for explained propagation */
  void setProofForPropExp(TNode lit, Node exp, std::shared_ptr<ProofNode> pf);
  /** Get the proof for the given key */
  std::shared_ptr<ProofNode> getProof(Node key);
  /** The proof node manager */
  ProofNodeManager* d_pnm;
  /**
   * A user-context-dependent map from lemmas and conflicts to proofs provided
   * by calls to setProofForConflict and setProofForLemma above.
   */
  NodeProofNodeMap d_proofs;
  /** A dummy context used by this class if none is provided */
  context::Context d_context;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__PROOF_GENERATOR_H */
