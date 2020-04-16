/*********************                                                        */
/*! \file proof_generator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The abstract proof generator class
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__PROOF_GENERATOR_H
#define CVC4__THEORY__PROOF_GENERATOR_H

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "expr/proof_node.h"
#include "theory/output_channel.h"

namespace CVC4 {
namespace theory {

/**
 * An abstract proof generator class, to be used in combination with
 * ProofOutputChannel (see theory/proof_output_channel.h).
 *
 * A proof generator is intended to be used as a utility in theory
 * solvers for constructing and storing proofs internally. A Theory may have
 * multiple instances of ProofGenerator objects, e.g. if it has more than one
 * way of justifying lemmas or conflicts.
 */
class ProofGenerator
{
 public:
  ProofGenerator();
  virtual ~ProofGenerator() {}
  /** Get the proof for conflict conf */
  virtual std::shared_ptr<ProofNode> getProofForConflict(Node conf) = 0;
  /** Get the proof for lemma lem */
  virtual std::shared_ptr<ProofNode> getProofForLemma(Node lem) = 0;
};

/**
 * A proven node is a pair (F, G) where F is a formula and G is a proof
 * generator that can construct a proof for F if asked.
 *
 * Notice that this is simply a convienence typedef for tracking what
 * lemmas are proven by which generators. However, the construction of
 * ProvenNode object are not protected.
 */
class ProvenNode
{
 public:
  ProvenNode(Node n, ProofGenerator* g = nullptr);
  ~ProvenNode() {}
  /** get node */
  Node getNode() const;
  /** get generator */
  ProofGenerator* getGenerator() const;
  /** is null? */
  bool isNull() const;
  /** The null proven node */
  static ProvenNode null();

 private:
  /** The node of this proof */
  Node d_node;
  /** The generator for the node */
  ProofGenerator* d_gen;
};

/**
 * An eager proof generator, with explicit proof caching.
 *
 * The intended use of this class is to store proofs for lemmas and conflicts
 * at the time they are sent out on the ProofOutputChannel. This means that the
 * getProofForConflict and getProofForLemma methods are lookups in a
 * (user-context depedent) map, the field d_proofs below.
 *
 * In detail, the method setProofForConflict(conf, pf) should be called prior to
 * calling ProofOutputChannel(ProvenNode(conf,X)), where X is this generator.
 * Similarly for setProofForLemma.
 *
 * A clean usage of this class in combination with ProofOutputChannel is the
 * following:
 * //-----------------------------------------------------------
 *   class MyEagerProofGenerator : public EagerProofGenerator
 *   {
 *     public:
 *      ProvenNode getProvenConflictByMethodX(...)
 *      {
 *        Node conf = [construct conflict];
 *        std::shared_ptr<ProofNode> pf = [construct its proof];
 *        setProofForConflict(conf, pf);
 *        return std::pair<Node, ProofGenerator * >( conf, this );
 *      }
 *   };
 *   // [1] Make objects given user context u and output channel out
 *   MyEagerProofGenerator epg(u);
 *   ProofOutputChannel poc(out, u);
 *
 *   // [2] Assume epg realizes there is a conflict. We have it store the proof
 *   // internally and return the conflict node paired with epg.
 *   ProvenNode pconf = epg.getProvenConflictByMethodX(...);
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
  EagerProofGenerator(context::UserContext* u, ProofNodeManager* pnm);
  ~EagerProofGenerator() {}
  /** Get the proof for conflict conf. */
  std::shared_ptr<ProofNode> getProofForConflict(Node conf) override;
  /** Get the proof for lemma lem. */
  std::shared_ptr<ProofNode> getProofForLemma(Node lem) override;
  //--------------------------------------- common proofs
  /**
   * This returns the proven node corresponding to the splitting lemma
   * (or f (not f)) and this generator. The method registers its proof in the
   * map maintained by this class. The return value can safely be passed to
   * ProofOutputChannel::sendLemma.
   */
  ProvenNode registerSplit(Node f);
  //--------------------------------------- end common proofs
 protected:
  /** Set that pf is the proof for conflict conf */
  void setProofForConflict(Node conf, std::shared_ptr<ProofNode> pf);
  /** Set that pf is the proof for lemma lem */
  void setProofForLemma(Node lem, std::shared_ptr<ProofNode> pf);
  /** Get the proof for the given key */
  std::shared_ptr<ProofNode> getProof(Node key);
  /** The proof node manager */
  ProofNodeManager* d_pnm;
  /**
   * A user-context-dependent map from lemmas and conflicts to proofs provided
   * by calls to setProofForConflict and setProofForLemma above.
   */
  NodeProofNodeMap d_proofs;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__PROOF_GENERATOR_H */
