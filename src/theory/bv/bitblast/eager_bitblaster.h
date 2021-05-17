/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Liana Hadarean, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bitblaster for the eager BV solver.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__BITBLAST__EAGER_BITBLASTER_H
#define CVC5__THEORY__BV__BITBLAST__EAGER_BITBLASTER_H

#include <memory>
#include <unordered_set>

#include "theory/bv/bitblast/bitblaster.h"

#include "prop/sat_solver.h"

namespace cvc5 {
namespace theory {
namespace bv {

class BitblastingRegistrar;
class BVSolverLazy;

class EagerBitblaster : public TBitblaster<Node>
{
 public:
  EagerBitblaster(BVSolverLazy* theory_bv, context::Context* context);
  ~EagerBitblaster();

  void addAtom(TNode atom);
  void makeVariable(TNode node, Bits& bits) override;
  void bbTerm(TNode node, Bits& bits) override;
  void bbAtom(TNode node) override;
  Node getBBAtom(TNode node) const override;
  bool hasBBAtom(TNode atom) const override;
  void bbFormula(TNode formula);
  void storeBBAtom(TNode atom, Node atom_bb) override;
  void storeBBTerm(TNode node, const Bits& bits) override;

  bool assertToSat(TNode node, bool propagate = true);
  bool solve();
  bool solve(const std::vector<Node>& assumptions);
  bool collectModelInfo(TheoryModel* m, bool fullModel);

 private:
  context::Context* d_context;

  typedef std::unordered_set<TNode> TNodeSet;
  std::unique_ptr<prop::SatSolver> d_satSolver;
  std::unique_ptr<BitblastingRegistrar> d_bitblastingRegistrar;

  BVSolverLazy* d_bv;
  TNodeSet d_bbAtoms;
  TNodeSet d_variables;

  // This is either an MinisatEmptyNotify or NULL.
  std::unique_ptr<MinisatEmptyNotify> d_notify;

  Node getModelFromSatSolver(TNode a, bool fullModel) override;
  prop::SatSolver* getSatSolver() override { return d_satSolver.get(); }
  bool isSharedTerm(TNode node);
};

class BitblastingRegistrar : public prop::Registrar
{
 public:
  BitblastingRegistrar(EagerBitblaster* bb) : d_bitblaster(bb) {}
  void preRegister(Node n) override { d_bitblaster->bbAtom(n); }

 private:
  EagerBitblaster* d_bitblaster;
};

}  // namespace bv
}  // namespace theory
}  // namespace cvc5
#endif  //  CVC5__THEORY__BV__BITBLAST__EAGER_BITBLASTER_H
