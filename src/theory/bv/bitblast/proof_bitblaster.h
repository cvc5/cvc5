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
 * A bit-blaster wrapper around BBSimple for proof logging.
 */
#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__BITBLAST__PROOF_BITBLASTER_H
#define CVC5__THEORY__BV__BITBLAST__PROOF_BITBLASTER_H

#include "theory/bv/bitblast/simple_bitblaster.h"

namespace cvc5 {

class TConvProofGenerator;

namespace theory {
namespace bv {

class BBProof
{
  using Bits = std::vector<Node>;

 public:
  BBProof(TheoryState* state, ProofNodeManager* pnm, TConvProofGenerator* tcpg);
  ~BBProof();

  /** Bit-blast atom 'node'. */
  void bbAtom(TNode node);
  /** Check if atom was already bit-blasted. */
  bool hasBBAtom(TNode atom) const;
  /** Check if term was already bit-blasted. */
  bool hasBBTerm(TNode node) const;
  /** Get bit-blasted node stored for atom. */
  Node getStoredBBAtom(TNode node);
  /** Collect model values for all relevant terms given in 'relevantTerms'. */
  bool collectModelValues(TheoryModel* m, const std::set<Node>& relevantTerms);

 private:
  /** Map node kinds to proof rules. */
  static std::unordered_map<Kind, PfRule, kind::KindHashFunction>
      s_kindToPfRule;

  /** Return true if proofs are enabled. */
  bool isProofsEnabled() const;

  /** The associated simple bit-blaster. */
  std::unique_ptr<BBSimple> d_bb;
  /** The associated proof node manager. */
  ProofNodeManager* d_pnm;
  /** The associated term conversion proof generator. */
  TConvProofGenerator* d_tcpg;
  /** Map bit-vector nodes to bit-blasted nodes. */
  std::unordered_map<Node, Node, NodeHashFunction> d_bbMap;
};

}  // namespace bv
}  // namespace theory
}  // namespace cvc5
#endif
