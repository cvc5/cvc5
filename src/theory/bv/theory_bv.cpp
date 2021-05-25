/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Andrew Reynolds, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Theory of bit-vectors.
 */

#include "theory/bv/theory_bv.h"

#include "options/bv_options.h"
#include "options/smt_options.h"
#include "proof/proof_checker.h"
#include "smt/smt_statistics_registry.h"
#include "theory/bv/bv_solver_bitblast.h"
#include "theory/bv/bv_solver_lazy.h"
#include "theory/bv/bv_solver_simple.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/ee_setup_info.h"
#include "theory/trust_substitutions.h"

namespace cvc5 {
namespace theory {
namespace bv {

TheoryBV::TheoryBV(context::Context* c,
                   context::UserContext* u,
                   OutputChannel& out,
                   Valuation valuation,
                   const LogicInfo& logicInfo,
                   ProofNodeManager* pnm,
                   std::string name)
    : Theory(THEORY_BV, c, u, out, valuation, logicInfo, pnm, name),
      d_internal(nullptr),
      d_rewriter(),
      d_state(c, u, valuation),
      d_im(*this, d_state, nullptr, "theory::bv::"),
      d_notify(d_im),
      d_stats("theory::bv::")
{
  switch (options::bvSolver())
  {
    case options::BVSolver::BITBLAST:
      d_internal.reset(new BVSolverBitblast(&d_state, d_im, pnm));
      break;

    case options::BVSolver::LAZY:
      d_internal.reset(new BVSolverLazy(*this, c, u, pnm, name));
      break;

    default:
      AlwaysAssert(options::bvSolver() == options::BVSolver::SIMPLE);
      d_internal.reset(new BVSolverSimple(&d_state, d_im, pnm));
  }
  d_theoryState = &d_state;
  d_inferManager = &d_im;
}

TheoryBV::~TheoryBV() {}

TheoryRewriter* TheoryBV::getTheoryRewriter() { return &d_rewriter; }

ProofRuleChecker* TheoryBV::getProofChecker()
{
  if (options::bvSolver() == options::BVSolver::SIMPLE)
  {
    return static_cast<BVSolverSimple*>(d_internal.get())->getProofChecker();
  }
  return nullptr;
}

bool TheoryBV::needsEqualityEngine(EeSetupInfo& esi)
{
  bool need_ee = d_internal->needsEqualityEngine(esi);

  /* Set up default notify class for equality engine. */
  if (need_ee && esi.d_notify == nullptr)
  {
    esi.d_notify = &d_notify;
    esi.d_name = "theory::bv::ee";
  }

  return need_ee;
}

void TheoryBV::finishInit()
{
  // these kinds are semi-evaluated in getModelValue (applications of this
  // kind are treated as variables)
  getValuation().setSemiEvaluatedKind(kind::BITVECTOR_ACKERMANNIZE_UDIV);
  getValuation().setSemiEvaluatedKind(kind::BITVECTOR_ACKERMANNIZE_UREM);
  d_internal->finishInit();

  eq::EqualityEngine* ee = getEqualityEngine();
  if (ee)
  {
    // The kinds we are treating as function application in congruence
    ee->addFunctionKind(kind::BITVECTOR_CONCAT, true);
    //    ee->addFunctionKind(kind::BITVECTOR_AND);
    //    ee->addFunctionKind(kind::BITVECTOR_OR);
    //    ee->addFunctionKind(kind::BITVECTOR_XOR);
    //    ee->addFunctionKind(kind::BITVECTOR_NOT);
    //    ee->addFunctionKind(kind::BITVECTOR_NAND);
    //    ee->addFunctionKind(kind::BITVECTOR_NOR);
    //    ee->addFunctionKind(kind::BITVECTOR_XNOR);
    //    ee->addFunctionKind(kind::BITVECTOR_COMP);
    ee->addFunctionKind(kind::BITVECTOR_MULT, true);
    ee->addFunctionKind(kind::BITVECTOR_ADD, true);
    ee->addFunctionKind(kind::BITVECTOR_EXTRACT, true);
    //    ee->addFunctionKind(kind::BITVECTOR_SUB);
    //    ee->addFunctionKind(kind::BITVECTOR_NEG);
    //    ee->addFunctionKind(kind::BITVECTOR_UDIV);
    //    ee->addFunctionKind(kind::BITVECTOR_UREM);
    //    ee->addFunctionKind(kind::BITVECTOR_SDIV);
    //    ee->addFunctionKind(kind::BITVECTOR_SREM);
    //    ee->addFunctionKind(kind::BITVECTOR_SMOD);
    //    ee->addFunctionKind(kind::BITVECTOR_SHL);
    //    ee->addFunctionKind(kind::BITVECTOR_LSHR);
    //    ee->addFunctionKind(kind::BITVECTOR_ASHR);
    //    ee->addFunctionKind(kind::BITVECTOR_ULT);
    //    ee->addFunctionKind(kind::BITVECTOR_ULE);
    //    ee->addFunctionKind(kind::BITVECTOR_UGT);
    //    ee->addFunctionKind(kind::BITVECTOR_UGE);
    //    ee->addFunctionKind(kind::BITVECTOR_SLT);
    //    ee->addFunctionKind(kind::BITVECTOR_SLE);
    //    ee->addFunctionKind(kind::BITVECTOR_SGT);
    //    ee->addFunctionKind(kind::BITVECTOR_SGE);
    ee->addFunctionKind(kind::BITVECTOR_TO_NAT);
    ee->addFunctionKind(kind::INT_TO_BITVECTOR);
  }
}

void TheoryBV::preRegisterTerm(TNode node)
{
  d_internal->preRegisterTerm(node);

  eq::EqualityEngine* ee = getEqualityEngine();
  if (ee)
  {
    if (node.getKind() == kind::EQUAL)
    {
      ee->addTriggerPredicate(node);
    }
    else
    {
      ee->addTerm(node);
    }
  }
}

bool TheoryBV::preCheck(Effort e) { return d_internal->preCheck(e); }

void TheoryBV::postCheck(Effort e) { d_internal->postCheck(e); }

bool TheoryBV::preNotifyFact(
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  return d_internal->preNotifyFact(atom, pol, fact, isPrereg, isInternal);
}

void TheoryBV::notifyFact(TNode atom, bool pol, TNode fact, bool isInternal)
{
  d_internal->notifyFact(atom, pol, fact, isInternal);
}

bool TheoryBV::needsCheckLastEffort()
{
  return d_internal->needsCheckLastEffort();
}

bool TheoryBV::collectModelValues(TheoryModel* m, const std::set<Node>& termSet)
{
  return d_internal->collectModelValues(m, termSet);
}

void TheoryBV::propagate(Effort e) { return d_internal->propagate(e); }

Theory::PPAssertStatus TheoryBV::ppAssert(
    TrustNode tin, TrustSubstitutionMap& outSubstitutions)
{
  TNode in = tin.getNode();
  Kind k = in.getKind();
  if (k == kind::EQUAL)
  {
    // Substitute variables
    if (in[0].isVar() && isLegalElimination(in[0], in[1]))
    {
      ++d_stats.d_solveSubstitutions;
      outSubstitutions.addSubstitutionSolved(in[0], in[1], tin);
      return Theory::PP_ASSERT_STATUS_SOLVED;
    }
    if (in[1].isVar() && isLegalElimination(in[1], in[0]))
    {
      ++d_stats.d_solveSubstitutions;
      outSubstitutions.addSubstitutionSolved(in[1], in[0], tin);
      return Theory::PP_ASSERT_STATUS_SOLVED;
    }
    /**
     * Eliminate extract over bit-vector variables.
     *
     * Given x[h:l] = c, where c is a constant and x is a variable.
     *
     * We rewrite to:
     *
     * x = sk1::c       if l == 0, where bw(sk1) = bw(x)-1-h
     * x = c::sk2       if h == bw(x)-1, where bw(sk2) = l
     * x = sk1::c::sk2  otherwise, where bw(sk1) = bw(x)-1-h and bw(sk2) = l
     */
    Node node = Rewriter::rewrite(in);
    if ((node[0].getKind() == kind::BITVECTOR_EXTRACT && node[1].isConst())
        || (node[1].getKind() == kind::BITVECTOR_EXTRACT
            && node[0].isConst()))
    {
      Node extract = node[0].isConst() ? node[1] : node[0];
      if (extract[0].isVar())
      {
        Node c = node[0].isConst() ? node[0] : node[1];

        uint32_t high = utils::getExtractHigh(extract);
        uint32_t low = utils::getExtractLow(extract);
        uint32_t var_bw = utils::getSize(extract[0]);
        std::vector<Node> children;

        // create sk1 with size bw(x)-1-h
        if (low == 0 || high != var_bw - 1)
        {
          Assert(high != var_bw - 1);
          uint32_t skolem_size = var_bw - high - 1;
          Node skolem = utils::mkVar(skolem_size);
          children.push_back(skolem);
        }

        children.push_back(c);

        // create sk2 with size l
        if (high == var_bw - 1 || low != 0)
        {
          Assert(low != 0);
          uint32_t skolem_size = low;
          Node skolem = utils::mkVar(skolem_size);
          children.push_back(skolem);
        }

        Node concat = utils::mkConcat(children);
        Assert(utils::getSize(concat) == utils::getSize(extract[0]));
        if (isLegalElimination(extract[0], concat))
        {
          outSubstitutions.addSubstitutionSolved(extract[0], concat, tin);
          return Theory::PP_ASSERT_STATUS_SOLVED;
        }
      }
    }
  }
  return Theory::PP_ASSERT_STATUS_UNSOLVED;
}

TrustNode TheoryBV::ppRewrite(TNode t, std::vector<SkolemLemma>& lems)
{
  // first, see if we need to expand definitions
  TrustNode texp = d_rewriter.expandDefinition(t);
  if (!texp.isNull())
  {
    return texp;
  }
  return d_internal->ppRewrite(t);
}

void TheoryBV::presolve() { d_internal->presolve(); }

EqualityStatus TheoryBV::getEqualityStatus(TNode a, TNode b)
{
  return d_internal->getEqualityStatus(a, b);
}

TrustNode TheoryBV::explain(TNode node) { return d_internal->explain(node); }

void TheoryBV::notifySharedTerm(TNode t)
{
  d_internal->notifySharedTerm(t);
}

void TheoryBV::ppStaticLearn(TNode in, NodeBuilder& learned)
{
  d_internal->ppStaticLearn(in, learned);
}

bool TheoryBV::applyAbstraction(const std::vector<Node>& assertions,
                                std::vector<Node>& new_assertions)
{
  return d_internal->applyAbstraction(assertions, new_assertions);
}

TheoryBV::Statistics::Statistics(const std::string& name)
    : d_solveSubstitutions(
        smtStatisticsRegistry().registerInt(name + "NumSolveSubstitutions"))
{
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5
