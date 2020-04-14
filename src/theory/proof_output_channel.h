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

namespace CVC4 {
namespace theory {

/** An abstract proof generator class */
class ProofGenerator
{
 public:
  ProofGenerator();
  virtual ~ProofGenerator() {}
  /** Get the proof for lemma lem */
  virtual std::shared_ptr<ProofNode> getProof(Node lem) = 0;
};

/** An eager proof generator, with explicit lemma caching */
class EagerProofGenerator : public ProofGenerator
{
 public:
  EagerProofGenerator(context::UserContext* u);
  ~EagerProofGenerator(){}
  /** Set that pf is the proof for conflict conf */
  void setProofForConflict(Node conf, std::shared_ptr<ProofNode> pf);
  /** Set that pf is the proof for lemma lem */
  void setProofForLemma(Node lem, std::shared_ptr<ProofNode> pf);
  /** Get the proof for lemma lem */
  std::shared_ptr<ProofNode> getProof(Node lem) override;
 protected:
  /** 
   * A user-context-dependent map from lemmas and conflicts to proofs provided
   * by calls to setProofForConflict and setProofForLemma above.
   */
  NodeProofNodeMap d_proofs; 
};

/**
 * A layer on top of an output channel to ensure proofs are constructed and
 * available.
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
   * by the generator pfg.
   */
  void conflict(Node conf, ProofGenerator* pfg);
  /**
   * Send lem on the output channel of this class whose proof can be generated
   * by the generator pfg.
   */
  LemmaStatus lemma(Node lem,
                    ProofGenerator* pfg,
                    bool removable = false,
                    bool preprocess = false,
                    bool sendAtoms = false);

  /**
   * Get proof for formula n. This returns the corresponding proof for formula
   * n, where n is either:
   * (1) some lem passed in a call to lemma(...), or
   * (2) conf.negate() for some conf passed in a call to conflict(...).
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
