/*********************                                                        */
/*! \file bv_solver_bitblast.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bit-blasting solver
 **
 ** Bit-blasting solver that supports multiple SAT backends.
 **/

#include "theory/bv/bv_solver_bitblast.h"

#include "prop/sat_solver_factory.h"
#include "smt/smt_statistics_registry.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/theory_model.h"

namespace CVC4 {
namespace theory {
namespace bv {

BVSolverBitblast::BVSolverBitblast(TheoryState* s,
                                   TheoryInferenceManager& inferMgr,
                                   ProofNodeManager* pnm)
    : BVSolver(*s, inferMgr),
      d_bitblaster(new BBSimple(s)),
      d_nullRegistrar(new prop::NullRegistrar()),
      d_nullContext(new context::Context()),
      d_facts(s->getSatContext()),
      d_epg(pnm ? new EagerProofGenerator(pnm, s->getUserContext(), "")
                : nullptr)
{
  if (pnm != nullptr)
  {
    d_bvProofChecker.registerTo(pnm->getChecker());
  }

  d_satSolver.reset(prop::SatSolverFactory::createCadical(
      smtStatisticsRegistry(), "BVSolverBitblast"));
  d_cnfStream.reset(new prop::CnfStream(d_satSolver.get(),
                                        d_nullRegistrar.get(),
                                        d_nullContext.get(),
                                        nullptr,
                                        smt::currentResourceManager()));
}

void BVSolverBitblast::postCheck(Theory::Effort level)
{
  if (level != Theory::Effort::EFFORT_FULL)
  {
    return;
  }

  std::vector<prop::SatLiteral> assumptions;
  std::unordered_map<prop::SatLiteral, TNode, prop::SatLiteralHashFunction>
      node_map;
  for (const TNode fact : d_facts)
  {
    Node bb_fact = Rewriter::rewrite(d_bitblaster->getStoredBBAtom(fact));
    prop::SatLiteral lit = d_cnfStream->getLiteral(bb_fact);
    assumptions.push_back(lit);
    node_map.emplace(lit, fact);
  }

  prop::SatValue val = d_satSolver->solve(assumptions);

  if (val == prop::SatValue::SAT_VALUE_FALSE)
  {
    std::vector<prop::SatLiteral> unsat_assumptions;
    d_satSolver->getUnsatAssumptions(unsat_assumptions);
    std::vector<Node> conflict;

    for (const prop::SatLiteral& lit : unsat_assumptions)
    {
      conflict.push_back(node_map[lit]);
    }

    NodeManager* nm = NodeManager::currentNM();
    Assert(unsat_assumptions.size() > 0);
    d_inferManager.conflict(nm->mkAnd(conflict));
  }
}

void BVSolverBitblast::bbFact(TNode fact)
{
  d_bitblaster->bbAtom(fact);
  Node atom_bb = Rewriter::rewrite(d_bitblaster->getStoredBBAtom(fact));
  d_cnfStream->ensureLiteral(atom_bb);
}

bool BVSolverBitblast::preNotifyFact(
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  bbFact(fact);
  d_facts.push_back(fact);
  return false;
}

bool BVSolverBitblast::collectModelValues(TheoryModel* m,
                                          const std::set<Node>& termSet)
{
  for (const auto& term : termSet)
  {
    if (!d_bitblaster->isVariable(term))
    {
      continue;
    }

    Node value = getValueFromSatSolver(term);
    Assert(value.isConst());
    if (!m->assertEquality(term, value, true))
    {
      return false;
    }
  }
  return true;
}

Node BVSolverBitblast::getValueFromSatSolver(TNode node)
{
  if (!d_bitblaster->hasBBTerm(node))
  {
    return utils::mkConst(utils::getSize(node), 0u);
  }

  std::vector<Node> bits;
  d_bitblaster->getBBTerm(node, bits);
  Integer value(0), one(1), zero(0), bit;
  for (size_t i = 0, size = bits.size(), j = size - 1; i < size; ++i, --j)
  {
    if (d_cnfStream->hasLiteral(bits[j]))
    {
      prop::SatLiteral lit = d_cnfStream->getLiteral(bits[j]);
      prop::SatValue val = d_satSolver->modelValue(lit);
      bit = val == prop::SatValue::SAT_VALUE_TRUE ? one : zero;
    }
    else
    {
      bit = zero;
    }
    value = value * 2 + bit;
  }
  return utils::mkConst(bits.size(), value);
}

}  // namespace bv
}  // namespace theory
}  // namespace CVC4
