/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Liana Hadarean, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bitblaster base class that contains default strategies for bitblasting.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__BITBLAST__BITBLASTER_H
#define CVC5__THEORY__BV__BITBLAST__BITBLASTER_H

#include <vector>

#include "theory/bv/bitblast/bitblast_strategies_template.h"
#include "util/resource_manager.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

/**
 * The Bitblaster that manages the mapping between Nodes
 * and their bitwise definition
 */
template <class T>
class TBitblaster
{
 protected:
  typedef std::vector<T> Bits;
  typedef void (*TermBBStrategy)(TNode, Bits&, TBitblaster<T>*);
  typedef T (*AtomBBStrategy)(TNode, TBitblaster<T>*);

  // function tables for the various bitblasting strategies indexed by node kind
  TermBBStrategy d_termBBStrategies[static_cast<uint32_t>(Kind::LAST_KIND)];
  AtomBBStrategy d_atomBBStrategies[static_cast<uint32_t>(Kind::LAST_KIND)];

 private:
  void initAtomBBStrategies();
  void initTermBBStrategies();

 public:
  TBitblaster();
  virtual ~TBitblaster() = default;

  /** Bit-blast atom 'node'. */
  virtual void bbAtom(TNode node) = 0;
  /** Check if atom was already bit-blasted. */
  virtual bool hasBBAtom(TNode atom) const = 0;
  /** Get bit-blasted atom. */
  virtual T getBBAtom(TNode atom) const = 0;

  /** Bit-blast term 'node' and return bit-blasted 'bits'. */
  virtual void bbTerm(TNode node, Bits& bits) = 0;
  /** Check if term was already bit-blasted. */
  virtual bool hasBBTerm(TNode node) const = 0;
  /** Fills 'bits' with generated bits of term 'node'. */
  virtual void getBBTerm(TNode node, Bits& bits) const = 0;

  /** Create a single bit given an atom 'node'. */
  virtual T makeAtom(TNode node) = 0;
  /** Create 'bits' for variable 'var'. */
  virtual void makeVariable(TNode node, Bits& bits) = 0;
};

// Bitblaster implementation

template <class T>
void TBitblaster<T>::initAtomBBStrategies()
{
  for (auto& atomBBStrategy : d_atomBBStrategies)
  {
    atomBBStrategy = UndefinedAtomBBStrategy<T>;
  }
  // clang-format off
  // setting default bb strategies for atoms
  d_atomBBStrategies[static_cast<uint32_t>(Kind::EQUAL)]         = DefaultEqBB<T>;
  d_atomBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_ULT)] = DefaultUltBB<T>;
  d_atomBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_ULE)] = DefaultUleBB<T>;
  d_atomBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_UGT)] = DefaultUgtBB<T>;
  d_atomBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_UGE)] = DefaultUgeBB<T>;
  d_atomBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_SLT)] = DefaultSltBB<T>;
  d_atomBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_SLE)] = DefaultSleBB<T>;
  d_atomBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_SGT)] = DefaultSgtBB<T>;
  d_atomBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_SGE)] = DefaultSgeBB<T>;
  // clang-format on
}

template <class T>
void TBitblaster<T>::initTermBBStrategies()
{
  for (auto& termBBStrategy : d_termBBStrategies)
  {
    termBBStrategy = DefaultVarBB<T>;
  }
  // clang-format off
  // setting default bb strategies for terms
  d_termBBStrategies[static_cast<uint32_t>(Kind::CONST_BITVECTOR)]        = DefaultConstBB<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_NOT)]          = DefaultNotBB<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_CONCAT)]       = DefaultConcatBB<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_AND)]          = DefaultAndBB<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_OR)]           = DefaultOrBB<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_XOR)]          = DefaultXorBB<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_XNOR)]         = DefaultXnorBB<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_NAND)]         = DefaultNandBB<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_NOR)]          = DefaultNorBB<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_COMP)]         = DefaultCompBB<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_MULT)]         = DefaultMultBB<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_ADD)]          = DefaultAddBB<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_SUB)]          = DefaultSubBB<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_NEG)]          = DefaultNegBB<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_UDIV)]         = DefaultUdivBB<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_UREM)]         = DefaultUremBB<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_SDIV)]         = UndefinedTermBBStrategy<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_SREM)]         = UndefinedTermBBStrategy<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_SMOD)]         = UndefinedTermBBStrategy<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_SHL)]          = DefaultShlBB<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_LSHR)]         = DefaultLshrBB<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_ASHR)]         = DefaultAshrBB<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_ULTBV)]        = DefaultUltbvBB<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_SLTBV)]        = DefaultSltbvBB<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_ITE)]          = DefaultIteBB<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_EXTRACT)]      = DefaultExtractBB<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_REPEAT)]       = DefaultRepeatBB<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_ZERO_EXTEND)]  = DefaultZeroExtendBB<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_SIGN_EXTEND)]  = DefaultSignExtendBB<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_ROTATE_RIGHT)] = DefaultRotateRightBB<T>;
  d_termBBStrategies[static_cast<uint32_t>(Kind::BITVECTOR_ROTATE_LEFT)]  = DefaultRotateLeftBB<T>;
  // clang-format on
}

template <class T>
TBitblaster<T>::TBitblaster()
{
  initAtomBBStrategies();
  initTermBBStrategies();
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BV__BITBLAST__BITBLASTER_H */
