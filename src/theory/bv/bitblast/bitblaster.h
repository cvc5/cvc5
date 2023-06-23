/******************************************************************************
 * Top contributors (to current version):
 *   Liana Hadarean, Mathias Preiner, Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Wrapper around the SAT solver used for bitblasting.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__BITBLAST__BITBLASTER_H
#define CVC5__THEORY__BV__BITBLAST__BITBLASTER_H

#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "expr/node.h"
#include "prop/cnf_stream.h"
#include "prop/registrar.h"
#include "prop/sat_solver.h"
#include "prop/sat_solver_types.h"
#include "theory/bv/bitblast/bitblast_strategies_template.h"
#include "theory/rewriter.h"
#include "theory/theory.h"
#include "theory/valuation.h"
#include "util/resource_manager.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

typedef std::unordered_set<Node> NodeSet;
typedef std::unordered_set<TNode> TNodeSet;

/**
 * The Bitblaster that manages the mapping between Nodes
 * and their bitwise definition
 *
 */

template <class T>
class TBitblaster
{
 protected:
  typedef std::vector<T> Bits;
  typedef std::unordered_map<Node, Bits> TermDefMap;
  typedef std::unordered_set<TNode> TNodeSet;
  typedef std::unordered_map<Node, Node> ModelCache;

  typedef void (*TermBBStrategy)(TNode, Bits&, TBitblaster<T>*);
  typedef T (*AtomBBStrategy)(TNode, TBitblaster<T>*);

  // caches and mappings
  TermDefMap d_termCache;
  ModelCache d_modelCache;
  // sat solver used for bitblasting and associated CnfStream
  std::unique_ptr<context::Context> d_nullContext;
  std::unique_ptr<prop::CnfStream> d_cnfStream;

  void initAtomBBStrategies();
  void initTermBBStrategies();

 protected:
  /// function tables for the various bitblasting strategies indexed by node
  /// kind
  TermBBStrategy d_termBBStrategies[kind::LAST_KIND];
  AtomBBStrategy d_atomBBStrategies[kind::LAST_KIND];
  virtual Node getModelFromSatSolver(TNode node, bool fullModel) = 0;
  virtual prop::SatSolver* getSatSolver() = 0;


 public:
  TBitblaster();
  virtual ~TBitblaster() {}
  virtual void bbAtom(TNode node) = 0;
  virtual void bbTerm(TNode node, Bits& bits) = 0;
  virtual void makeVariable(TNode node, Bits& bits) = 0;
  virtual T getBBAtom(TNode atom) const = 0;
  virtual bool hasBBAtom(TNode atom) const = 0;
  virtual void storeBBAtom(TNode atom, T atom_bb) = 0;

  bool hasBBTerm(TNode node) const;
  void getBBTerm(TNode node, Bits& bits) const;
  virtual void storeBBTerm(TNode term, const Bits& bits);

  /**
   * Return a constant representing the value of a in the  model.
   * If fullModel is true set unconstrained bits to 0. If not return
   * NullNode() for a fully or partially unconstrained.
   *
   */
  Node getTermModel(TNode node, bool fullModel);
  void invalidateModelCache();
};

// Bitblaster implementation

template <class T>
void TBitblaster<T>::initAtomBBStrategies()
{
  for (int i = 0; i < kind::LAST_KIND; ++i)
  {
    d_atomBBStrategies[i] = UndefinedAtomBBStrategy<T>;
  }
  /// setting default bb strategies for atoms
  d_atomBBStrategies[kind::EQUAL] = DefaultEqBB<T>;
  d_atomBBStrategies[kind::BITVECTOR_ULT] = DefaultUltBB<T>;
  d_atomBBStrategies[kind::BITVECTOR_ULE] = DefaultUleBB<T>;
  d_atomBBStrategies[kind::BITVECTOR_UGT] = DefaultUgtBB<T>;
  d_atomBBStrategies[kind::BITVECTOR_UGE] = DefaultUgeBB<T>;
  d_atomBBStrategies[kind::BITVECTOR_SLT] = DefaultSltBB<T>;
  d_atomBBStrategies[kind::BITVECTOR_SLE] = DefaultSleBB<T>;
  d_atomBBStrategies[kind::BITVECTOR_SGT] = DefaultSgtBB<T>;
  d_atomBBStrategies[kind::BITVECTOR_SGE] = DefaultSgeBB<T>;
}

template <class T>
void TBitblaster<T>::initTermBBStrategies()
{
  for (int i = 0; i < kind::LAST_KIND; ++i)
  {
    d_termBBStrategies[i] = DefaultVarBB<T>;
  }
  /// setting default bb strategies for terms:
  d_termBBStrategies[kind::CONST_BITVECTOR] = DefaultConstBB<T>;
  d_termBBStrategies[kind::BITVECTOR_NOT] = DefaultNotBB<T>;
  d_termBBStrategies[kind::BITVECTOR_CONCAT] = DefaultConcatBB<T>;
  d_termBBStrategies[kind::BITVECTOR_AND] = DefaultAndBB<T>;
  d_termBBStrategies[kind::BITVECTOR_OR] = DefaultOrBB<T>;
  d_termBBStrategies[kind::BITVECTOR_XOR] = DefaultXorBB<T>;
  d_termBBStrategies[kind::BITVECTOR_XNOR] = DefaultXnorBB<T>;
  d_termBBStrategies[kind::BITVECTOR_NAND] = DefaultNandBB<T>;
  d_termBBStrategies[kind::BITVECTOR_NOR] = DefaultNorBB<T>;
  d_termBBStrategies[kind::BITVECTOR_COMP] = DefaultCompBB<T>;
  d_termBBStrategies[kind::BITVECTOR_MULT] = DefaultMultBB<T>;
  d_termBBStrategies[kind::BITVECTOR_ADD] = DefaultAddBB<T>;
  d_termBBStrategies[kind::BITVECTOR_SUB] = DefaultSubBB<T>;
  d_termBBStrategies[kind::BITVECTOR_NEG] = DefaultNegBB<T>;
  d_termBBStrategies[kind::BITVECTOR_UDIV] = DefaultUdivBB<T>;
  d_termBBStrategies[kind::BITVECTOR_UREM] = DefaultUremBB<T>;
  d_termBBStrategies[kind::BITVECTOR_SDIV] = UndefinedTermBBStrategy<T>;
  d_termBBStrategies[kind::BITVECTOR_SREM] = UndefinedTermBBStrategy<T>;
  d_termBBStrategies[kind::BITVECTOR_SMOD] = UndefinedTermBBStrategy<T>;
  d_termBBStrategies[kind::BITVECTOR_SHL] = DefaultShlBB<T>;
  d_termBBStrategies[kind::BITVECTOR_LSHR] = DefaultLshrBB<T>;
  d_termBBStrategies[kind::BITVECTOR_ASHR] = DefaultAshrBB<T>;
  d_termBBStrategies[kind::BITVECTOR_ULTBV] = DefaultUltbvBB<T>;
  d_termBBStrategies[kind::BITVECTOR_SLTBV] = DefaultSltbvBB<T>;
  d_termBBStrategies[kind::BITVECTOR_ITE] = DefaultIteBB<T>;
  d_termBBStrategies[kind::BITVECTOR_EXTRACT] = DefaultExtractBB<T>;
  d_termBBStrategies[kind::BITVECTOR_REPEAT] = DefaultRepeatBB<T>;
  d_termBBStrategies[kind::BITVECTOR_ZERO_EXTEND] = DefaultZeroExtendBB<T>;
  d_termBBStrategies[kind::BITVECTOR_SIGN_EXTEND] = DefaultSignExtendBB<T>;
  d_termBBStrategies[kind::BITVECTOR_ROTATE_RIGHT] = DefaultRotateRightBB<T>;
  d_termBBStrategies[kind::BITVECTOR_ROTATE_LEFT] = DefaultRotateLeftBB<T>;
}

template <class T>
TBitblaster<T>::TBitblaster()
    : d_termCache(),
      d_modelCache(),
      d_nullContext(new context::Context()),
      d_cnfStream()
{
  initAtomBBStrategies();
  initTermBBStrategies();
}

template <class T>
bool TBitblaster<T>::hasBBTerm(TNode node) const
{
  return d_termCache.find(node) != d_termCache.end();
}
template <class T>
void TBitblaster<T>::getBBTerm(TNode node, Bits& bits) const
{
  Assert(hasBBTerm(node));
  bits = d_termCache.find(node)->second;
}

template <class T>
void TBitblaster<T>::storeBBTerm(TNode node, const Bits& bits)
{
  d_termCache.insert(std::make_pair(node, bits));
}

template <class T>
void TBitblaster<T>::invalidateModelCache()
{
  d_modelCache.clear();
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BV__BITBLAST__BITBLASTER_H */
