/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A bit-blaster wrapper around NodeBitblaster for proof logging.
 */
#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__BITBLAST__PROOF_BITBLASTER_H
#define CVC5__THEORY__BV__BITBLAST__PROOF_BITBLASTER_H

#include "expr/term_context.h"
#include "theory/bv/bitblast/node_bitblaster.h"

namespace cvc5 {

class TConvProofGenerator;

namespace theory {
namespace bv {

class BBProof
{
  using Bits = std::vector<Node>;

 public:
  BBProof(TheoryState* state, ProofNodeManager* pnm, bool fineGrained);
  ~BBProof();

  /** Bit-blast atom 'node'. */
  void bbAtom(TNode node);
  /** Check if atom was already bit-blasted. */
  bool hasBBAtom(TNode atom) const;
  /** Check if term was already bit-blasted. */
  bool hasBBTerm(TNode node) const;
  /** Get bit-blasted node stored for atom. */
  Node getStoredBBAtom(TNode node);
  /** Get bit-blasted bits stored for node. */
  void getBBTerm(TNode node, Bits& bits) const;
  /** Collect model values for all relevant terms given in 'relevantTerms'. */
  bool collectModelValues(TheoryModel* m, const std::set<Node>& relevantTerms);

  TConvProofGenerator* getProofGenerator();

 private:
  /** Return true if proofs are enabled. */
  bool isProofsEnabled() const;

  /** The associated simple bit-blaster. */
  std::unique_ptr<NodeBitblaster> d_bb;
  /** The associated proof node manager. */
  ProofNodeManager* d_pnm;
  /** Term context for d_tcpg to not rewrite below BV leafs. */
  std::unique_ptr<TermContext> d_tcontext;
  /** The associated term conversion proof generator. */
  std::unique_ptr<TConvProofGenerator> d_tcpg;
  /** Map bit-vector nodes to bit-blasted nodes. */
  std::unordered_map<Node, Node> d_bbMap;

  bool d_recordFineGrainedProofs;
};

}  // namespace bv
}  // namespace theory
}  // namespace cvc5
#endif
