/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Gereon Kremer, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bit-blasting solver that supports multiple SAT backends.
 */

#include "theory/bv/bv_solver_bitblast.h"

#include "options/bv_options.h"
#include "prop/sat_solver_factory.h"
#include "smt/smt_statistics_registry.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/theory_model.h"

namespace cvc5 {
namespace theory {
namespace bv {

BVSolverBitblast::BVSolverBitblast(TheoryState* s,
                                   TheoryInferenceManager& inferMgr,
                                   ProofNodeManager* pnm)
    : BVSolver(*s, inferMgr),
      d_bitblaster(new BBSimple(s)),
      d_nullRegistrar(new prop::NullRegistrar()),
      d_nullContext(new context::Context()),
      d_bbFacts(s->getSatContext()),
      d_assumptions(s->getSatContext()),
      d_invalidateModelCache(s->getSatContext(), true),
      d_inSatMode(s->getSatContext(), false),
      d_epg(pnm ? new EagerProofGenerator(pnm, s->getUserContext(), "")
                : nullptr),
      d_factLiteralCache(s->getSatContext()),
      d_literalFactCache(s->getSatContext()),
      d_propagate(options::bitvectorPropagate())
{
  if (pnm != nullptr)
  {
    d_bvProofChecker.registerTo(pnm->getChecker());
  }

  switch (options::bvSatSolver())
  {
    case options::SatSolverMode::CRYPTOMINISAT:
      d_satSolver.reset(prop::SatSolverFactory::createCryptoMinisat(
          smtStatisticsRegistry(), "theory::bv::BVSolverBitblast"));
      break;
    default:
      d_satSolver.reset(prop::SatSolverFactory::createCadical(
          smtStatisticsRegistry(), "theory::bv::BVSolverBitblast"));
  }
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
    /* Do bit-level propagation only if the SAT solver supports it. */
    if (!d_propagate || !d_satSolver->setPropagateOnly())
    {
      return;
    }
  }

  /* Process bit-blast queue and store SAT literals. */
  while (!d_bbFacts.empty())
  {
    Node fact = d_bbFacts.front();
    d_bbFacts.pop();
    /* Bit-blast fact and cache literal. */
    if (d_factLiteralCache.find(fact) == d_factLiteralCache.end())
    {
      d_bitblaster->bbAtom(fact);
      Node bb_fact = d_bitblaster->getStoredBBAtom(fact);
      d_cnfStream->ensureLiteral(bb_fact);

      prop::SatLiteral lit = d_cnfStream->getLiteral(bb_fact);
      d_factLiteralCache[fact] = lit;
      d_literalFactCache[lit] = fact;
    }
    d_assumptions.push_back(d_factLiteralCache[fact]);
  }

  d_invalidateModelCache.set(true);
  std::vector<prop::SatLiteral> assumptions(d_assumptions.begin(),
                                            d_assumptions.end());
  prop::SatValue val = d_satSolver->solve(assumptions);
  d_inSatMode = val == prop::SatValue::SAT_VALUE_TRUE;
  Debug("bv-bitblast") << "d_inSatMode: " << d_inSatMode << std::endl;

  if (val == prop::SatValue::SAT_VALUE_FALSE)
  {
    std::vector<prop::SatLiteral> unsat_assumptions;
    d_satSolver->getUnsatAssumptions(unsat_assumptions);
    Assert(unsat_assumptions.size() > 0);

    std::vector<Node> conflict;
    for (const prop::SatLiteral& lit : unsat_assumptions)
    {
      conflict.push_back(d_literalFactCache[lit]);
      Debug("bv-bitblast") << "unsat assumption (" << lit
                           << "): " << conflict.back() << std::endl;
    }

    NodeManager* nm = NodeManager::currentNM();
    d_im.conflict(nm->mkAnd(conflict), InferenceId::BV_BITBLAST_CONFLICT);
  }
}

bool BVSolverBitblast::preNotifyFact(
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  d_bbFacts.push_back(fact);
  return false;  // Return false to enable equality engine reasoning in Theory.
}

TrustNode BVSolverBitblast::explain(TNode n)
{
  Debug("bv-bitblast") << "explain called on " << n << std::endl;
  return d_im.explainLit(n);
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

    Node value = getValueFromSatSolver(term, true);
    Assert(value.isConst());
    if (!m->assertEquality(term, value, true))
    {
      return false;
    }
  }
  return true;
}

EqualityStatus BVSolverBitblast::getEqualityStatus(TNode a, TNode b)
{
  Debug("bv-bitblast") << "getEqualityStatus on " << a << " and " << b
                       << std::endl;
  if (!d_inSatMode)
  {
    Debug("bv-bitblast") << EQUALITY_UNKNOWN << std::endl;
    return EQUALITY_UNKNOWN;
  }
  Node value_a = getValue(a);
  Node value_b = getValue(b);

  if (value_a == value_b)
  {
    Debug("bv-bitblast") << EQUALITY_TRUE_IN_MODEL << std::endl;
    return EQUALITY_TRUE_IN_MODEL;
  }
  Debug("bv-bitblast") << EQUALITY_FALSE_IN_MODEL << std::endl;
  return EQUALITY_FALSE_IN_MODEL;
}

Node BVSolverBitblast::getValueFromSatSolver(TNode node, bool initialize)
{
  if (node.isConst())
  {
    return node;
  }

  if (!d_bitblaster->hasBBTerm(node))
  {
    return initialize ? utils::mkConst(utils::getSize(node), 0u) : Node();
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
      if (!initialize) return Node();
      bit = zero;
    }
    value = value * 2 + bit;
  }
  return utils::mkConst(bits.size(), value);
}

Node BVSolverBitblast::getValue(TNode node)
{
  if (d_invalidateModelCache.get())
  {
    d_modelCache.clear();
  }
  d_invalidateModelCache.set(false);

  std::vector<TNode> visit;

  TNode cur;
  visit.push_back(node);
  do
  {
    cur = visit.back();
    visit.pop_back();

    auto it = d_modelCache.find(cur);
    if (it != d_modelCache.end() && !it->second.isNull())
    {
      continue;
    }

    if (d_bitblaster->hasBBTerm(cur))
    {
      Node value = getValueFromSatSolver(cur, false);
      if (value.isConst())
      {
        d_modelCache[cur] = value;
        continue;
      }
    }
    if (Theory::isLeafOf(cur, theory::THEORY_BV))
    {
      Node value = getValueFromSatSolver(cur, true);
      d_modelCache[cur] = value;
      continue;
    }

    if (it == d_modelCache.end())
    {
      visit.push_back(cur);
      d_modelCache.emplace(cur, Node());
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
    else if (it->second.isNull())
    {
      NodeBuilder nb(cur.getKind());
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        nb << cur.getOperator();
      }

      std::unordered_map<Node, Node, NodeHashFunction>::iterator iit;
      for (const TNode& child : cur)
      {
        iit = d_modelCache.find(child);
        Assert(iit != d_modelCache.end());
        Assert(iit->second.isConst());
        nb << iit->second;
      }
      it->second = Rewriter::rewrite(nb.constructNode());
    }
  } while (!visit.empty());

  auto it = d_modelCache.find(node);
  Assert(it != d_modelCache.end());
  return it->second;
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5
