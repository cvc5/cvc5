/*********************                                                        */
/*! \file simple_bitblaster.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bitblaster for simple BV solver.
 **
 **/
#include "cvc4_private.h"

#ifndef CVC4__THEORY__BV__BITBLAST_SIMPLE_BITBLASTER_H
#define CVC4__THEORY__BV__BITBLAST_SIMPLE_BITBLASTER_H

#include "theory/bv/bitblast/lazy_bitblaster.h"

namespace CVC4 {
namespace theory {
namespace bv {

/**
 * Implementation of a simple Node-based bit-blaster.
 *
 * Implements the bare minimum to bit-blast bit-vector atoms/terms.
 */
class BBSimple : public TBitblaster<Node>
{
  using Bits = std::vector<Node>;

 public:
  BBSimple(TheoryState* state);
  ~BBSimple() = default;

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

  /** Collect model values for all relevant terms given in 'relevantTerms'. */
  bool collectModelValues(TheoryModel* m, const std::set<Node>& relevantTerms);

  prop::SatSolver* getSatSolver() override { Unreachable(); }

 private:
  /** Query SAT solver for assignment of node 'a'. */
  Node getModelFromSatSolver(TNode a, bool fullModel) override;

  /** Caches variables for which we already created bits. */
  TNodeSet d_variables;
  /** Stores bit-blasted atoms. */
  std::unordered_map<Node, Node, NodeHashFunction> d_bbAtoms;
  /** Theory state. */
  TheoryState* d_state;
};

}  // namespace bv
}  // namespace theory
}  // namespace CVC4

#endif
