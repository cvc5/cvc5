/*********************                                                        */
/*! \file proof_bitblaster.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A bit-blaster wrapper around BBSimple for proof logging.
 **/
#include "cvc4_private.h"

#ifndef CVC4__THEORY__BV__BITBLAST__PROOF_BITBLASTER_H
#define CVC4__THEORY__BV__BITBLAST__PROOF_BITBLASTER_H

#include "theory/bv/bitblast/simple_bitblaster.h"

namespace CVC4 {
namespace theory {
namespace bv {

class BBProof
{
  using Bits = std::vector<Node>;

 public:
  BBProof(TheoryState* state);
  ~BBProof() = default;

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
  std::unique_ptr<BBSimple> d_bb;
};

}  // namespace bv
}  // namespace theory
}  // namespace CVC4
#endif
