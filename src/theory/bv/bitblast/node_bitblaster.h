/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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

#include "theory/theory.h"
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
  explicit NodeBitblaster(Env& env);
  ~NodeBitblaster() override = default;

  /** Bit-blast atom 'node'. */
  void bbAtom(TNode node) override;
  /** Check if atom was already bit-blasted. */
  bool hasBBAtom(TNode atom) const override;
  /** Get bit-blasted node stored for atom. */
  Node getBBAtom(TNode atom) const override;

  /** Bit-blast term 'node' and return bit-blasted 'bits'. */
  void bbTerm(TNode node, Bits& bits) override;
  /** Check if term was already bit-blasted. */
  bool hasBBTerm(TNode node) const override;
  /** Fills 'bits' with generated bits of term 'node'. */
  void getBBTerm(TNode node, Bits& bits) const override;

  /** Get bit for atom, returns 'atom' itself since it's Boolean. */
  Node makeAtom(TNode node) override;
  /** Create 'bits' for variable 'var'. */
  void makeVariable(TNode var, Bits& bits) override;
  /** Checks whether node is a variable introduced via `makeVariable`.*/
  bool isVariable(TNode node) const;
  /** Add d_variables to termSet. */
  void collectVariables(std::set<Node>& termSet) const;

  /**
   * Bit-blast `node` and return the result without applying any rewrites.
   * This method does not use the cache of the result for `node`.
   */
  Node applyAtomBBStrategy(TNode node);

 protected:
  /** Store Boolean node representing the bit-blasted atom. */
  void storeBBAtom(TNode atom, Node atom_bb);
  /** Store bits of bit-blasted term. */
  void storeBBTerm(TNode node, const Bits& bits);

 private:
  /** Caches variables for which we already created bits. */
  std::unordered_set<Node> d_variables;
  /** Stores bit-blasted atoms. */
  std::unordered_map<Node, Node> d_bbAtoms;
  /** Stores bit-blasted terms. */
  std::unordered_map<Node, Bits> d_bbTerms;
};

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif
