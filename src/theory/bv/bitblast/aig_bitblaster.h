/******************************************************************************
 * Top contributors (to current version):
 *   Liana Hadarean, Mathias Preiner, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * AIG Bitblaster based on ABC.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__BITBLAST__AIG_BITBLASTER_H
#define CVC5__THEORY__BV__BITBLAST__AIG_BITBLASTER_H

#include "theory/bv/bitblast/bitblaster.h"

class Abc_Obj_t_;
typedef Abc_Obj_t_ Abc_Obj_t;

class Abc_Ntk_t_;
typedef Abc_Ntk_t_ Abc_Ntk_t;

class Abc_Aig_t_;
typedef Abc_Aig_t_ Abc_Aig_t;

class Cnf_Dat_t_;
typedef Cnf_Dat_t_ Cnf_Dat_t;

namespace cvc5 {
namespace prop {
class SatSolver;
}
namespace theory {
namespace bv {

#ifdef CVC5_USE_ABC

class AigBitblaster : public TBitblaster<Abc_Obj_t*>
{
 public:
  AigBitblaster();
  ~AigBitblaster();

  void makeVariable(TNode node, Bits& bits) override;
  void bbTerm(TNode node, Bits& bits) override;
  void bbAtom(TNode node) override;
  Abc_Obj_t* bbFormula(TNode formula);
  bool solve(TNode query);
  static Abc_Aig_t* currentAigM();
  static Abc_Ntk_t* currentAigNtk();

 private:
  typedef std::unordered_map<TNode, Abc_Obj_t*> TNodeAigMap;
  typedef std::unordered_map<Node, Abc_Obj_t*> NodeAigMap;

  static thread_local Abc_Ntk_t* s_abcAigNetwork;
  std::unique_ptr<context::Context> d_nullContext;
  std::unique_ptr<prop::SatSolver> d_satSolver;
  TNodeAigMap d_aigCache;
  NodeAigMap d_bbAtoms;

  NodeAigMap d_nodeToAigInput;
  // the thing we are checking for sat
  Abc_Obj_t* d_aigOutputNode;

  std::unique_ptr<MinisatEmptyNotify> d_notify;

  void addAtom(TNode atom);
  void simplifyAig();
  void storeBBAtom(TNode atom, Abc_Obj_t* atom_bb) override;
  Abc_Obj_t* getBBAtom(TNode atom) const override;
  bool hasBBAtom(TNode atom) const override;
  void cacheAig(TNode node, Abc_Obj_t* aig);
  bool hasAig(TNode node);
  Abc_Obj_t* getAig(TNode node);
  Abc_Obj_t* mkInput(TNode input);
  bool hasInput(TNode input);
  void convertToCnfAndAssert();
  void assertToSatSolver(Cnf_Dat_t* pCnf);
  Node getModelFromSatSolver(TNode a, bool fullModel) override
  {
    Unreachable();
  }

  prop::SatSolver* getSatSolver() override { return d_satSolver.get(); }

  class Statistics
  {
   public:
    IntStat d_numClauses;
    IntStat d_numVariables;
    TimerStat d_simplificationTime;
    TimerStat d_cnfConversionTime;
    TimerStat d_solveTime;
    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;
};

#else /* CVC5_USE_ABC */

/**
 * Dummy version of the AigBitblaster class that cannot be instantiated s.t. we
 * can declare `std::unique_ptr<AigBitblaster>` without ABC.
 */
class AigBitblaster : public TBitblaster<Abc_Obj_t*>
{
  AigBitblaster() = delete;
};

#endif /* CVC5_USE_ABC */

}  // namespace bv
}  // namespace theory
}  // namespace cvc5

#endif  //  CVC5__THEORY__BV__BITBLAST__AIG_BITBLASTER_H
