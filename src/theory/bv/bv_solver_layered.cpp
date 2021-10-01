/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Liana Hadarean, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Layered bit-vector solver.
 */

#include "theory/bv/bv_solver_layered.h"

#include "expr/node_algorithm.h"
#include "options/bv_options.h"
#include "options/smt_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/bv/abstraction.h"
#include "theory/bv/bv_eager_solver.h"
#include "theory/bv/bv_subtheory_algebraic.h"
#include "theory/bv/bv_subtheory_bitblast.h"
#include "theory/bv/bv_subtheory_core.h"
#include "theory/bv/bv_subtheory_inequality.h"
#include "theory/bv/theory_bv_rewrite_rules_normalization.h"
#include "theory/bv/theory_bv_rewrite_rules_simplification.h"
#include "theory/bv/theory_bv_rewriter.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/theory_model.h"

using namespace cvc5::theory::bv::utils;

namespace cvc5 {
namespace theory {
namespace bv {

BVSolverLayered::BVSolverLayered(Env& env,
                                 TheoryBV& bv,
                                 context::Context* c,
                                 context::UserContext* u,
                                 ProofNodeManager* pnm,
                                 std::string name)
    : BVSolver(env, bv.d_state, bv.d_im),
      d_bv(bv),
      d_context(c),
      d_alreadyPropagatedSet(c),
      d_sharedTermsSet(c),
      d_subtheories(),
      d_subtheoryMap(),
      d_statistics(),
      d_lemmasAdded(c, false),
      d_conflict(c, false),
      d_invalidateModelCache(c, true),
      d_literalsToPropagate(c),
      d_literalsToPropagateIndex(c, 0),
      d_propagatedBy(c),
      d_eagerSolver(),
      d_abstractionModule(new AbstractionModule(getStatsPrefix(THEORY_BV))),
      d_calledPreregister(false)
{
  if (options().bv.bitblastMode == options::BitblastMode::EAGER)
  {
    d_eagerSolver.reset(new EagerBitblastSolver(c, this));
    return;
  }

  if (options().bv.bitvectorEqualitySolver)
  {
    d_subtheories.emplace_back(new CoreSolver(c, this));
    d_subtheoryMap[SUB_CORE] = d_subtheories.back().get();
  }

  if (options().bv.bitvectorInequalitySolver)
  {
    d_subtheories.emplace_back(new InequalitySolver(c, u, this));
    d_subtheoryMap[SUB_INEQUALITY] = d_subtheories.back().get();
  }

  if (options().bv.bitvectorAlgebraicSolver)
  {
    d_subtheories.emplace_back(new AlgebraicSolver(c, this));
    d_subtheoryMap[SUB_ALGEBRAIC] = d_subtheories.back().get();
  }

  BitblastSolver* bb_solver = new BitblastSolver(c, this);
  if (options().bv.bvAbstraction)
  {
    bb_solver->setAbstraction(d_abstractionModule.get());
  }
  d_subtheories.emplace_back(bb_solver);
  d_subtheoryMap[SUB_BITBLAST] = bb_solver;
}

BVSolverLayered::~BVSolverLayered() {}

bool BVSolverLayered::needsEqualityEngine(EeSetupInfo& esi)
{
  CoreSolver* core = (CoreSolver*)d_subtheoryMap[SUB_CORE];
  if (core)
  {
    return core->needsEqualityEngine(esi);
  }
  // otherwise we don't use an equality engine
  return false;
}

void BVSolverLayered::finishInit()
{
  CoreSolver* core = (CoreSolver*)d_subtheoryMap[SUB_CORE];
  if (core)
  {
    // must finish initialization in the core solver
    core->finishInit();
  }
}

void BVSolverLayered::spendResource(Resource r) { d_im.spendResource(r); }

BVSolverLayered::Statistics::Statistics()
    : d_avgConflictSize(smtStatisticsRegistry().registerAverage(
        "theory::bv::lazy::AvgBVConflictSize")),
      d_solveTimer(smtStatisticsRegistry().registerTimer(
          "theory::bv::lazy::solveTimer")),
      d_numCallsToCheckFullEffort(smtStatisticsRegistry().registerInt(
          "theory::bv::lazy::NumFullCheckCalls")),
      d_numCallsToCheckStandardEffort(smtStatisticsRegistry().registerInt(
          "theory::bv::lazy::NumStandardCheckCalls")),
      d_weightComputationTimer(smtStatisticsRegistry().registerTimer(
          "theory::bv::lazy::weightComputationTimer")),
      d_numMultSlice(smtStatisticsRegistry().registerInt(
          "theory::bv::lazy::NumMultSliceApplied"))
{
}

void BVSolverLayered::preRegisterTerm(TNode node)
{
  d_calledPreregister = true;
  Debug("bitvector-preregister")
      << "BVSolverLayered::preRegister(" << node << ")" << std::endl;

  if (options().bv.bitblastMode == options::BitblastMode::EAGER)
  {
    // the aig bit-blaster option is set heuristically
    // if bv abstraction is used
    if (!d_eagerSolver->isInitialized())
    {
      d_eagerSolver->initialize();
    }

    if (node.getKind() == kind::BITVECTOR_EAGER_ATOM)
    {
      Node formula = node[0];
      d_eagerSolver->assertFormula(formula);
    }
    return;
  }

  for (unsigned i = 0; i < d_subtheories.size(); ++i)
  {
    d_subtheories[i]->preRegister(node);
  }

  // AJR : equality solver currently registers all terms to ExtTheory, if we
  // want a lazy reduction without the bv equality solver, need to call this
  // d_bv.d_extTheory->registerTermRec( node );
}

void BVSolverLayered::sendConflict()
{
  Assert(d_conflict);
  if (d_conflictNode.isNull())
  {
    return;
  }
  else
  {
    Debug("bitvector") << indent() << "BVSolverLayered::check(): conflict "
                       << d_conflictNode << std::endl;
    d_im.conflict(d_conflictNode, InferenceId::BV_LAYERED_CONFLICT);
    d_statistics.d_avgConflictSize << d_conflictNode.getNumChildren();
    d_conflictNode = Node::null();
  }
}

void BVSolverLayered::checkForLemma(TNode fact)
{
  if (fact.getKind() == kind::EQUAL)
  {
    NodeManager* nm = NodeManager::currentNM();
    if (fact[0].getKind() == kind::BITVECTOR_UREM)
    {
      TNode urem = fact[0];
      TNode result = fact[1];
      TNode divisor = urem[1];
      Node result_ult_div = nm->mkNode(kind::BITVECTOR_ULT, result, divisor);
      Node divisor_eq_0 =
          nm->mkNode(kind::EQUAL, divisor, mkZero(getSize(divisor)));
      Node split = nm->mkNode(
          kind::OR, divisor_eq_0, nm->mkNode(kind::NOT, fact), result_ult_div);
      lemma(split);
    }
    if (fact[1].getKind() == kind::BITVECTOR_UREM)
    {
      TNode urem = fact[1];
      TNode result = fact[0];
      TNode divisor = urem[1];
      Node result_ult_div = nm->mkNode(kind::BITVECTOR_ULT, result, divisor);
      Node divisor_eq_0 =
          nm->mkNode(kind::EQUAL, divisor, mkZero(getSize(divisor)));
      Node split = nm->mkNode(
          kind::OR, divisor_eq_0, nm->mkNode(kind::NOT, fact), result_ult_div);
      lemma(split);
    }
  }
}

bool BVSolverLayered::preCheck(Theory::Effort e)
{
  check(e);
  return true;
}

void BVSolverLayered::check(Theory::Effort e)
{
  if (done() && e < Theory::EFFORT_FULL)
  {
    return;
  }

  Debug("bitvector") << "BVSolverLayered::check(" << e << ")" << std::endl;
  TimerStat::CodeTimer codeTimer(d_statistics.d_solveTimer);
  // we may be getting new assertions so the model cache may not be sound
  d_invalidateModelCache.set(true);
  // if we are using the eager solver
  if (options().bv.bitblastMode == options::BitblastMode::EAGER)
  {
    // this can only happen on an empty benchmark
    if (!d_eagerSolver->isInitialized())
    {
      d_eagerSolver->initialize();
    }
    if (!Theory::fullEffort(e)) return;

    std::vector<TNode> assertions;
    while (!done())
    {
      TNode fact = get().d_assertion;
      Assert(fact.getKind() == kind::BITVECTOR_EAGER_ATOM);
      assertions.push_back(fact);
      d_eagerSolver->assertFormula(fact[0]);
    }

    bool ok = d_eagerSolver->checkSat();
    if (!ok)
    {
      if (assertions.size() == 1)
      {
        d_im.conflict(assertions[0], InferenceId::BV_LAYERED_CONFLICT);
        return;
      }
      Node conflict = utils::mkAnd(assertions);
      d_im.conflict(conflict, InferenceId::BV_LAYERED_CONFLICT);
      return;
    }
    return;
  }

  if (Theory::fullEffort(e))
  {
    ++(d_statistics.d_numCallsToCheckFullEffort);
  }
  else
  {
    ++(d_statistics.d_numCallsToCheckStandardEffort);
  }
  // if we are already in conflict just return the conflict
  if (inConflict())
  {
    sendConflict();
    return;
  }

  while (!done())
  {
    TNode fact = get().d_assertion;

    checkForLemma(fact);

    for (unsigned i = 0; i < d_subtheories.size(); ++i)
    {
      d_subtheories[i]->assertFact(fact);
    }
  }

  bool ok = true;
  bool complete = false;
  for (unsigned i = 0; i < d_subtheories.size(); ++i)
  {
    Assert(!inConflict());
    ok = d_subtheories[i]->check(e);
    complete = d_subtheories[i]->isComplete();

    if (!ok)
    {
      // if we are in a conflict no need to check with other theories
      Assert(inConflict());
      sendConflict();
      return;
    }
    if (complete)
    {
      // if the last subtheory was complete we stop
      break;
    }
  }
}

bool BVSolverLayered::collectModelValues(TheoryModel* m,
                                         const std::set<Node>& termSet)
{
  Assert(!inConflict());
  if (options().bv.bitblastMode == options::BitblastMode::EAGER)
  {
    if (!d_eagerSolver->collectModelInfo(m, true))
    {
      return false;
    }
  }
  for (unsigned i = 0; i < d_subtheories.size(); ++i)
  {
    if (d_subtheories[i]->isComplete())
    {
      return d_subtheories[i]->collectModelValues(m, termSet);
    }
  }
  return true;
}

Node BVSolverLayered::getModelValue(TNode var)
{
  Assert(!inConflict());
  for (unsigned i = 0; i < d_subtheories.size(); ++i)
  {
    if (d_subtheories[i]->isComplete())
    {
      return d_subtheories[i]->getModelValue(var);
    }
  }
  Unreachable();
}

void BVSolverLayered::propagate(Theory::Effort e)
{
  Debug("bitvector") << indent() << "BVSolverLayered::propagate()" << std::endl;
  if (options().bv.bitblastMode == options::BitblastMode::EAGER)
  {
    return;
  }

  if (inConflict())
  {
    return;
  }

  // go through stored propagations
  bool ok = true;
  for (; d_literalsToPropagateIndex < d_literalsToPropagate.size() && ok;
       d_literalsToPropagateIndex = d_literalsToPropagateIndex + 1)
  {
    TNode literal = d_literalsToPropagate[d_literalsToPropagateIndex];
    // temporary fix for incremental bit-blasting
    if (d_state.isSatLiteral(literal))
    {
      Debug("bitvector::propagate")
          << "BVSolverLayered:: propagating " << literal << "\n";
      ok = d_im.propagateLit(literal);
    }
  }

  if (!ok)
  {
    Debug("bitvector::propagate")
        << indent()
        << "BVSolverLayered::propagate(): conflict from theory engine"
        << std::endl;
    setConflict();
  }
}

void BVSolverLayered::presolve()
{
  Debug("bitvector") << "BVSolverLayered::presolve" << std::endl;
}

static int prop_count = 0;

bool BVSolverLayered::storePropagation(TNode literal, SubTheory subtheory)
{
  Debug("bitvector::propagate")
      << indent() << d_context->getLevel() << " "
      << "BVSolverLayered::storePropagation(" << literal << ", " << subtheory
      << ")" << std::endl;
  prop_count++;

  // If already in conflict, no more propagation
  if (d_conflict)
  {
    Debug("bitvector::propagate")
        << indent() << "BVSolverLayered::storePropagation(" << literal << ", "
        << subtheory << "): already in conflict" << std::endl;
    return false;
  }

  // If propagated already, just skip
  PropagatedMap::const_iterator find = d_propagatedBy.find(literal);
  if (find != d_propagatedBy.end())
  {
    return true;
  }
  else
  {
    bool polarity = literal.getKind() != kind::NOT;
    Node negatedLiteral = polarity ? literal.notNode() : (Node)literal[0];
    find = d_propagatedBy.find(negatedLiteral);
    if (find != d_propagatedBy.end() && (*find).second != subtheory)
    {
      // Safe to ignore this one, subtheory should produce a conflict
      return true;
    }

    d_propagatedBy[literal] = subtheory;
  }

  // Propagate differs depending on the subtheory
  // * bitblaster needs to be left alone until it's done, otherwise it doesn't
  //   know how to explain
  // * equality engine can propagate eagerly
  // TODO(2348): Determine if ok should be set by propagate. If not, remove ok.
  constexpr bool ok = true;
  if (subtheory == SUB_CORE)
  {
    d_im.propagateLit(literal);
    if (!ok)
    {
      setConflict();
    }
  }
  else
  {
    d_literalsToPropagate.push_back(literal);
  }
  return ok;

} /* BVSolverLayered::propagate(TNode) */

void BVSolverLayered::explain(TNode literal, std::vector<TNode>& assumptions)
{
  Assert(wasPropagatedBySubtheory(literal));
  SubTheory sub = getPropagatingSubtheory(literal);
  d_subtheoryMap[sub]->explain(literal, assumptions);
}

TrustNode BVSolverLayered::explain(TNode node)
{
  Debug("bitvector::explain")
      << "BVSolverLayered::explain(" << node << ")" << std::endl;
  std::vector<TNode> assumptions;

  // Ask for the explanation
  explain(node, assumptions);
  // this means that it is something true at level 0
  Node explanation;
  if (assumptions.size() == 0)
  {
    explanation = utils::mkTrue();
  }
  else
  {
    // return the explanation
    explanation = utils::mkAnd(assumptions);
  }
  Debug("bitvector::explain") << "BVSolverLayered::explain(" << node << ") => "
                              << explanation << std::endl;
  Debug("bitvector::explain") << "BVSolverLayered::explain done. \n";
  return TrustNode::mkTrustPropExp(node, explanation, nullptr);
}

void BVSolverLayered::notifySharedTerm(TNode t)
{
  Debug("bitvector::sharing")
      << indent() << "BVSolverLayered::notifySharedTerm(" << t << ")"
      << std::endl;
  d_sharedTermsSet.insert(t);
}

EqualityStatus BVSolverLayered::getEqualityStatus(TNode a, TNode b)
{
  if (options().bv.bitblastMode == options::BitblastMode::EAGER)
    return EQUALITY_UNKNOWN;
  Assert(options().bv.bitblastMode == options::BitblastMode::LAZY);
  for (unsigned i = 0; i < d_subtheories.size(); ++i)
  {
    EqualityStatus status = d_subtheories[i]->getEqualityStatus(a, b);
    if (status != EQUALITY_UNKNOWN)
    {
      return status;
    }
  }
  return EQUALITY_UNKNOWN;
  ;
}

bool BVSolverLayered::applyAbstraction(const std::vector<Node>& assertions,
                                       std::vector<Node>& new_assertions)
{
  bool changed =
      d_abstractionModule->applyAbstraction(assertions, new_assertions);
  if (changed && options().bv.bitblastMode == options::BitblastMode::EAGER
      && options().bv.bitvectorAig)
  {
    // disable AIG mode
    AlwaysAssert(!d_eagerSolver->isInitialized());
    d_eagerSolver->turnOffAig();
    d_eagerSolver->initialize();
  }
  return changed;
}

void BVSolverLayered::setConflict(Node conflict)
{
  if (options().bv.bvAbstraction)
  {
    NodeManager* const nm = NodeManager::currentNM();
    Node new_conflict = d_abstractionModule->simplifyConflict(conflict);

    std::vector<Node> lemmas;
    lemmas.push_back(new_conflict);
    d_abstractionModule->generalizeConflict(new_conflict, lemmas);
    for (unsigned i = 0; i < lemmas.size(); ++i)
    {
      lemma(nm->mkNode(kind::NOT, lemmas[i]));
    }
  }
  d_conflict = true;
  d_conflictNode = conflict;
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5
