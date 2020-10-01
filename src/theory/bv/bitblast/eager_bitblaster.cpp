/*********************                                                        */
/*! \file eager_bitblaster.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Mathias Preiner, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief
 **
 ** Bitblaster for the eager bv solver.
 **/

#include "theory/bv/bitblast/eager_bitblaster.h"

#include "cvc4_private.h"
#include "options/bv_options.h"
#include "prop/cnf_stream.h"
#include "prop/sat_solver_factory.h"
#include "smt/smt_engine.h"
#include "smt/smt_statistics_registry.h"
#include "theory/bv/bv_solver_lazy.h"
#include "theory/bv/theory_bv.h"
#include "theory/theory_model.h"

namespace CVC4 {
namespace theory {
namespace bv {

EagerBitblaster::EagerBitblaster(BVSolverLazy* theory_bv, context::Context* c)
    : TBitblaster<Node>(),
      d_context(c),
      d_satSolver(),
      d_bitblastingRegistrar(new BitblastingRegistrar(this)),
      d_bv(theory_bv),
      d_bbAtoms(),
      d_variables(),
      d_notify()
{
  prop::SatSolver *solver = nullptr;
  switch (options::bvSatSolver())
  {
    case options::SatSolverMode::MINISAT:
    {
      prop::BVSatSolverInterface* minisat =
          prop::SatSolverFactory::createMinisat(
              d_nullContext.get(), smtStatisticsRegistry(), "EagerBitblaster");
      d_notify.reset(new MinisatEmptyNotify());
      minisat->setNotify(d_notify.get());
      solver = minisat;
      break;
    }
    case options::SatSolverMode::CADICAL:
      solver = prop::SatSolverFactory::createCadical(smtStatisticsRegistry(),
                                                     "EagerBitblaster");
      break;
    case options::SatSolverMode::CRYPTOMINISAT:
      solver = prop::SatSolverFactory::createCryptoMinisat(
          smtStatisticsRegistry(), "EagerBitblaster");
      break;
    case options::SatSolverMode::KISSAT:
      solver = prop::SatSolverFactory::createKissat(smtStatisticsRegistry(),
                                                    "EagerBitblaster");
      break;
    default: Unreachable() << "Unknown SAT solver type";
  }
  d_satSolver.reset(solver);
  ResourceManager* rm = smt::currentResourceManager();
  d_cnfStream.reset(new prop::CnfStream(d_satSolver.get(),
                                        d_bitblastingRegistrar.get(),
                                        d_nullContext.get(),
                                        nullptr,
                                        rm,
                                        false,
                                        "EagerBitblaster"));
}

EagerBitblaster::~EagerBitblaster() {}

void EagerBitblaster::bbFormula(TNode node)
{
  /* For incremental eager solving we assume formulas at context levels > 1. */
  if (options::incrementalSolving() && d_context->getLevel() > 1)
  {
    d_cnfStream->ensureLiteral(node);
  }
  else
  {
    d_cnfStream->convertAndAssert(node, false, false);
  }
}

/**
 * Bitblasts the atom, assigns it a marker literal, adding it to the SAT solver
 * NOTE: duplicate clauses are not detected because of marker literal
 * @param node the atom to be bitblasted
 *
 */
void EagerBitblaster::bbAtom(TNode node)
{
  node = node.getKind() == kind::NOT ? node[0] : node;
  if (node.getKind() == kind::BITVECTOR_BITOF
      || node.getKind() == kind::CONST_BOOLEAN || hasBBAtom(node))
  {
    return;
  }

  Debug("bitvector-bitblast") << "Bitblasting node " << node << "\n";

  // the bitblasted definition of the atom
  Node normalized = Rewriter::rewrite(node);
  Node atom_bb =
      normalized.getKind() != kind::CONST_BOOLEAN
          ? d_atomBBStrategies[normalized.getKind()](normalized, this)
          : normalized;

  atom_bb = Rewriter::rewrite(atom_bb);

  // asserting that the atom is true iff the definition holds
  Node atom_definition =
      NodeManager::currentNM()->mkNode(kind::EQUAL, node, atom_bb);

  AlwaysAssert(options::bitblastMode() == options::BitblastMode::EAGER);
  storeBBAtom(node, atom_bb);
  d_cnfStream->convertAndAssert(atom_definition, false, false);
}

void EagerBitblaster::storeBBAtom(TNode atom, Node atom_bb) {
  d_bbAtoms.insert(atom);
}

void EagerBitblaster::storeBBTerm(TNode node, const Bits& bits) {
  d_termCache.insert(std::make_pair(node, bits));
}

bool EagerBitblaster::hasBBAtom(TNode atom) const {
  return d_bbAtoms.find(atom) != d_bbAtoms.end();
}

void EagerBitblaster::bbTerm(TNode node, Bits& bits) {
  Assert(node.getType().isBitVector());

  if (hasBBTerm(node)) {
    getBBTerm(node, bits);
    return;
  }

  d_bv->spendResource(ResourceManager::Resource::BitblastStep);
  Debug("bitvector-bitblast") << "Bitblasting node " << node << "\n";

  d_termBBStrategies[node.getKind()](node, bits, this);

  Assert(bits.size() == utils::getSize(node));

  storeBBTerm(node, bits);
}

void EagerBitblaster::makeVariable(TNode var, Bits& bits) {
  Assert(bits.size() == 0);
  for (unsigned i = 0; i < utils::getSize(var); ++i) {
    bits.push_back(utils::mkBitOf(var, i));
  }
  d_variables.insert(var);
}

Node EagerBitblaster::getBBAtom(TNode node) const { return node; }

/**
 * Calls the solve method for the Sat Solver.
 *
 * @return true for sat, and false for unsat
 */

bool EagerBitblaster::solve() {
  if (Trace.isOn("bitvector")) {
    Trace("bitvector") << "EagerBitblaster::solve(). \n";
  }
  Debug("bitvector") << "EagerBitblaster::solve(). \n";
  // TODO: clear some memory
  // if (something) {
  //   NodeManager* nm= NodeManager::currentNM();
  //   Rewriter::garbageCollect();
  //   nm->reclaimZombiesUntil(options::zombieHuntThreshold());
  // }
  return prop::SAT_VALUE_TRUE == d_satSolver->solve();
}

bool EagerBitblaster::solve(const std::vector<Node>& assumptions)
{
  std::vector<prop::SatLiteral> assumpts;
  for (const Node& assumption : assumptions)
  {
    Assert(d_cnfStream->hasLiteral(assumption));
    assumpts.push_back(d_cnfStream->getLiteral(assumption));
  }
  return prop::SAT_VALUE_TRUE == d_satSolver->solve(assumpts);
}

/**
 * Returns the value a is currently assigned to in the SAT solver
 * or null if the value is completely unassigned.
 *
 * @param a
 * @param fullModel whether to create a "full model," i.e., add
 * constants to equivalence classes that don't already have them
 *
 * @return
 */
Node EagerBitblaster::getModelFromSatSolver(TNode a, bool fullModel) {
  if (!hasBBTerm(a)) {
    return fullModel ? utils::mkConst(utils::getSize(a), 0u) : Node();
  }

  Bits bits;
  getBBTerm(a, bits);
  Integer value(0);
  for (int i = bits.size() - 1; i >= 0; --i) {
    prop::SatValue bit_value;
    if (d_cnfStream->hasLiteral(bits[i])) {
      prop::SatLiteral bit = d_cnfStream->getLiteral(bits[i]);
      bit_value = d_satSolver->value(bit);
      Assert(bit_value != prop::SAT_VALUE_UNKNOWN);
    } else {
      if (!fullModel) return Node();
      // unconstrained bits default to false
      bit_value = prop::SAT_VALUE_FALSE;
    }
    Integer bit_int =
        bit_value == prop::SAT_VALUE_TRUE ? Integer(1) : Integer(0);
    value = value * 2 + bit_int;
  }
  return utils::mkConst(bits.size(), value);
}

bool EagerBitblaster::collectModelInfo(TheoryModel* m, bool fullModel)
{
  NodeManager* nm = NodeManager::currentNM();

  // Collect the values for the bit-vector variables
  TNodeSet::iterator it = d_variables.begin();
  for (; it != d_variables.end(); ++it) {
    TNode var = *it;
    if (d_bv->isLeaf(var) || isSharedTerm(var) ||
        (var.isVar() && var.getType().isBoolean())) {
      // only shared terms could not have been bit-blasted
      Assert(hasBBTerm(var) || isSharedTerm(var));

      Node const_value = getModelFromSatSolver(var, true);

      if (const_value != Node()) {
        Debug("bitvector-model")
            << "EagerBitblaster::collectModelInfo (assert (= " << var << " "
            << const_value << "))\n";
        if (!m->assertEquality(var, const_value, true))
        {
          return false;
        }
      }
    }
  }

  // Collect the values for the Boolean variables
  std::vector<TNode> vars;
  d_cnfStream->getBooleanVariables(vars);
  for (TNode var : vars)
  {
    Assert(d_cnfStream->hasLiteral(var));
    prop::SatLiteral bit = d_cnfStream->getLiteral(var);
    prop::SatValue value = d_satSolver->value(bit);
    Assert(value != prop::SAT_VALUE_UNKNOWN);
    if (!m->assertEquality(
            var, nm->mkConst(value == prop::SAT_VALUE_TRUE), true))
    {
      return false;
    }
  }
  return true;
}

bool EagerBitblaster::isSharedTerm(TNode node) {
  return d_bv->d_sharedTermsSet.find(node) != d_bv->d_sharedTermsSet.end();
}


}  // namespace bv
}  // namespace theory
}  // namespace CVC4
