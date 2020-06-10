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
 * The intended usage of this class in combination with OutputChannel is
 * the following:
 * //-----------------------------------------------------------
 *   class MyEagerProofGenerator : public EagerProofGenerator
 *   {
 *     public:
 *      TrustNode getProvenConflictByMethodX(...)
 *      {
 *        // construct a conflict
 *        Node conf = [construct conflict];
 *        // construct a proof for conf
 *        std::shared_ptr<ProofNode> pf = [construct the proof for conf];
 *        // wrap the conflict in a trust node
 *        return mkTrustNode(conf,pf);
 *      }
 *   };
 *   // [1] Make objects given user context u and output channel out.
 *
 *   MyEagerProofGenerator epg(u);
 *   OutputChannel out;
 *
 *   // [2] Assume epg realizes there is a conflict. We have it store the proof
 *   // internally and return the conflict node paired with epg.
 *
 *   TrustNode pconf = epg.getProvenConflictByMethodX(...);
 *
 *   // [3] Send the conflict on the output channel.
 *
 *   out.trustedConflict(pconf);
 *
 *   // [4] The trust node has information about what is proven and who can
 *   // prove it, where this association is valid in the remainder of the user
 *   // context.
 *
 *   Node conf = pconf.getProven();
 *   ProofGenerator * pg = pconf.getGenerator();
 *   std::shared_ptr<ProofNode> pf = pg->getProofForConflict(conf);
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
  EagerProofGenerator(ProofNodeManager* pnm, context::Context* c = nullptr);
  ~EagerProofGenerator() {}
  /** Get the proof for formula f. */
  std::shared_ptr<ProofNode> getProofFor(Node f) override;
  /** Can we give the proof for formula f? */
  bool hasProofFor(Node f) override;
  /**
   * Set proof for fact f, called when pf is a proof of f.
   *
   * @param f The fact proven by pf,
   * @param pf The proof to store in this class.
   */
  void setProofFor(Node f, std::shared_ptr<ProofNode> pf);
  /**
   * Make trust node: wrap n in a trust node with this generator, and have it
   * store the proof pf to lemma or conflict n.
   *
   * @param n The proven node,
   * @param pf The proof of n,
   * @param isConflict Whether the returned trust node is a conflict (otherwise
   * it is a lemma),
   * @return The trust node corresponding to the fact that this generator has
   * a proof of n.
   */
  TrustNode mkTrustNode(Node n,
                        std::shared_ptr<ProofNode> pf,
                        bool isConflict = false);
  /**
   * Make trust node from a single step proof (with no premises). This is a
   * convenience function that avoids the need to explictly construct ProofNode
   * by the caller.
   *
   * @param n The proven node,
   * @param id The rule of the proof concluding n
   * @param args The arguments to the proof concluding n,
   * @param isConflict Whether the returned trust node is a conflict (otherwise
   * it is a lemma),
   * @return The trust node corresponding to the fact that this generator has
   * a proof of n.
   */
  TrustNode mkTrustNode(Node n,
                        PfRule id,
                        const std::vector<Node>& args,
                        bool isConflict = false);
  /**
   * Make trust node: wrap `exp => n` in a trust node with this generator, and
   * have it store the proof `pf` too.
   *
   * @param n The implication
   * @param exp A conjunction of literals that imply it
   * @param pf The proof of exp => n,
   * @return The trust node corresponding to the fact that this generator has
   * a proof of exp => n.
   */
  TrustNode mkTrustedPropagation(Node n,
                                 Node exp,
                                 std::shared_ptr<ProofNode> pf);
  //--------------------------------------- common proofs
  /**
   * This returns the trust node corresponding to the splitting lemma
   * (or f (not f)) and this generator. The method registers its proof in the
   * map maintained by this class.
   */
  TrustNode mkTrustNodeSplit(Node f);
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
  /** The proof node manager */
  ProofNodeManager* d_pnm;
  /** A dummy context used by this class if none is provided */
  context::Context d_context;
  /**
   * A user-context-dependent map from lemmas and conflicts to proofs provided
   * by calls to setProofForConflict and setProofForLemma above.
   */
  NodeProofNodeMap d_proofs;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__PROOF_GENERATOR_H */
