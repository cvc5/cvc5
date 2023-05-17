/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bitblaster used to bitblast to Boolean Nodes.
 */
#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__BITBLAST_NODE_BITBLASTER_H
#define CVC5__THEORY__BV__BITBLAST_NODE_BITBLASTER_H

#include "theory/bv/bitblast/bitblaster.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

/**
 * Implementation of a simple Node-based bit-blaster.
 *
 * Implements the bare minimum to bit-blast bit-vector atoms/terms.
 */
class NodeBitblaster : public TBitblaster<Node>, protected EnvObj
{
  using Bits = std::vector<Node>;

 public:
  NodeBitblaster(Env& env, TheoryState* state);
  ~NodeBitblaster() = default;

  /** Bit-blast term 'node' and return bit-blasted 'bits'. */
  void bbTerm(TNode node, Bits& bits) override;
  /** Bit-blast atom 'node'. */
  void bbAtom(TNode node) override;
  /** Get bit-blasted atom, returns 'atom' itself since it's Boolean. */
  Node getBBAtom(TNode atom) const override;
  /** Store Boolean node representing the bit-blasted atom. */
  void storeBBAtom(TNode atom, Node atom_bb) override;
  /** Store bits of bit-blasted term. */
  void storeBBTerm(TNode node, const Bits& bits) override;
  /** Check if atom was already bit-blasted. */
  bool hasBBAtom(TNode atom) const override;
  /** Get bit-blasted node stored for atom. */
  Node getStoredBBAtom(TNode node);
  /** Create 'bits' for variable 'var'. */
  void makeVariable(TNode var, Bits& bits) override;

  /** Add d_variables to termSet. */
  void computeRelevantTerms(std::set<Node>& termSet);
  /** Collect model values for all relevant terms given in 'relevantTerms'. */
  bool collectModelValues(TheoryModel* m, const std::set<Node>& relevantTerms);

  prop::SatSolver* getSatSolver() override { Unreachable(); }

  /** Checks whether node is a variable introduced via `makeVariable`.*/
  bool isVariable(TNode node);

  /**
   * Bit-blast `node` and return the result without applying any rewrites.
   *
   * This method is used by BBProof and does not cache the result for `node`.
   */
  Node applyAtomBBStrategy(TNode node);

 private:
  /** Query SAT solver for assignment of node 'a'. */
  Node getModelFromSatSolver(TNode a, bool fullModel) override;

  /** Caches variables for which we already created bits. */
  TNodeSet d_variables;
  /** Stores bit-blasted atoms. */
  std::unordered_map<Node, Node> d_bbAtoms;
  /** Theory state. */
  TheoryState* d_state;
};

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif
