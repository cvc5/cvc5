/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Andrew Reynolds, Liana Hadarean
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "theory/bv/bv_solver_bitblast.h"
#include "theory/bv/bv_solver_bitblast_internal.h"
#include "theory/bv/theory_bv_rewrite_rules_normalization.h"
#include "theory/bv/theory_bv_rewrite_rules_simplification.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/ee_setup_info.h"
#include "theory/trust_substitutions.h"
#include "theory/uf/equality_engine.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

TheoryBV::TheoryBV(Env& env,
                   OutputChannel& out,
                   Valuation valuation,
                   std::string name)
    : Theory(THEORY_BV, env, out, valuation, name),
      d_internal(nullptr),
      d_rewriter(),
      d_state(env, valuation),
      d_im(env, *this, d_state, "theory::bv::"),
      d_notify(d_im),
      d_invalidateModelCache(context(), true),
      d_stats(statisticsRegistry(), "theory::bv::")
{
  switch (options().bv.bvSolver)
  {
    case options::BVSolver::BITBLAST:
      d_internal.reset(new BVSolverBitblast(env, &d_state, d_im));
      break;

    default:
      AlwaysAssert(options().bv.bvSolver == options::BVSolver::BITBLAST_INTERNAL);
      d_internal.reset(new BVSolverBitblastInternal(d_env, &d_state, d_im));
  }
  d_theoryState = &d_state;
  d_inferManager = &d_im;
}

TheoryBV::~TheoryBV() {}

TheoryRewriter* TheoryBV::getTheoryRewriter() { return &d_rewriter; }

ProofRuleChecker* TheoryBV::getProofChecker()
{
  if (options().bv.bvSolver == options::BVSolver::BITBLAST_INTERNAL)
  {
    return static_cast<BVSolverBitblastInternal*>(d_internal.get())
        ->getProofChecker();
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
    bool eagerEval = options().bv.bvEagerEval;
    // The kinds we are treating as function application in congruence
    ee->addFunctionKind(kind::BITVECTOR_CONCAT, eagerEval);
    //    ee->addFunctionKind(kind::BITVECTOR_AND);
    //    ee->addFunctionKind(kind::BITVECTOR_OR);
    //    ee->addFunctionKind(kind::BITVECTOR_XOR);
    //    ee->addFunctionKind(kind::BITVECTOR_NOT);
    //    ee->addFunctionKind(kind::BITVECTOR_NAND);
    //    ee->addFunctionKind(kind::BITVECTOR_NOR);
    //    ee->addFunctionKind(kind::BITVECTOR_XNOR);
    //    ee->addFunctionKind(kind::BITVECTOR_COMP);
    ee->addFunctionKind(kind::BITVECTOR_MULT, eagerEval);
    ee->addFunctionKind(kind::BITVECTOR_ADD, eagerEval);
    ee->addFunctionKind(kind::BITVECTOR_EXTRACT, eagerEval);
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
      d_state.addEqualityEngineTriggerPredicate(node);
    }
    else
    {
      ee->addTerm(node);
    }
  }
}

bool TheoryBV::preCheck(Effort e) { return d_internal->preCheck(e); }

void TheoryBV::postCheck(Effort e)
{
  d_invalidateModelCache = true;
  d_internal->postCheck(e);
}

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

void TheoryBV::computeRelevantTerms(std::set<Node>& termSet)
{
  return d_internal->computeRelevantTerms(termSet);
}

bool TheoryBV::collectModelValues(TheoryModel* m, const std::set<Node>& termSet)
{
  return d_internal->collectModelValues(m, termSet);
}

void TheoryBV::propagate(Effort e) { return d_internal->propagate(e); }

Theory::PPAssertStatus TheoryBV::ppAssert(
    TrustNode tin, TrustSubstitutionMap& outSubstitutions)
{
  Kind k = tin.getNode().getKind();
  if (k == kind::EQUAL)
  {
    auto status = Theory::ppAssert(tin, outSubstitutions);
    if (status != Theory::PP_ASSERT_STATUS_UNSOLVED)
    {
      return status;
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
    Node node = rewrite(tin.getNode());
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
  Trace("theory-bv-pp-rewrite") << "ppRewrite " << t << "\n";
  Node res = t;
  if (options().bv.bitwiseEq && RewriteRule<BitwiseEq>::applies(t))
  {
    res = rewrite(RewriteRule<BitwiseEq>::run<false>(t));
  }
  // useful on QF_BV/space/ndist
  else if (RewriteRule<UltAddOne>::applies(t))
  {
    res = rewrite(RewriteRule<UltAddOne>::run<false>(t));
  }
  // Useful for BV/2017-Preiner-scholl-smt08, but not for QF_BV
  else if (options().bv.rwExtendEq)
  {
    if (RewriteRule<SignExtendEqConst>::applies(t))
    {
      res = RewriteRule<SignExtendEqConst>::run<false>(t);
    }
    else if (RewriteRule<ZeroExtendEqConst>::applies(t))
    {
      res = RewriteRule<ZeroExtendEqConst>::run<false>(t);
    }
  }

  Trace("theory-bv-pp-rewrite") << "to   " << res << "\n";
  if (res != t)
  {
    return TrustNode::mkTrustRewrite(t, res, nullptr);
  }

  return d_internal->ppRewrite(t);
}

void TheoryBV::presolve() { d_internal->presolve(); }

EqualityStatus TheoryBV::getEqualityStatus(TNode a, TNode b)
{
  EqualityStatus status = d_internal->getEqualityStatus(a, b);

  if (status == EqualityStatus::EQUALITY_UNKNOWN)
  {
    Node value_a = getValue(a);
    Node value_b = getValue(b);

    if (value_a.isNull() || value_b.isNull())
    {
      return status;
    }

    if (value_a == value_b)
    {
      Trace("theory-bv") << EQUALITY_TRUE_IN_MODEL << std::endl;
      return EQUALITY_TRUE_IN_MODEL;
    }
    Trace("theory-bv") << EQUALITY_FALSE_IN_MODEL << std::endl;
    return EQUALITY_FALSE_IN_MODEL;
  }
  return status;
}

TrustNode TheoryBV::explain(TNode node) { return d_internal->explain(node); }

void TheoryBV::notifySharedTerm(TNode t)
{
  d_internal->notifySharedTerm(t);
}

void TheoryBV::ppStaticLearn(TNode in, NodeBuilder& learned)
{
  if (in.getKind() == kind::EQUAL)
  {
    // Only useful in combination with --bv-intro-pow2 on
    // QF_BV/pspace/power2sum benchmarks.
    //
    // Matches for equality:
    //
    // (= (bvadd (bvshl 1 x) (bvshl 1 y)) (bvshl 1 z))
    //
    // and does case analysis on the sum of two power of twos.
    if ((in[0].getKind() == kind::BITVECTOR_ADD
         && in[1].getKind() == kind::BITVECTOR_SHL)
        || (in[1].getKind() == kind::BITVECTOR_ADD
            && in[0].getKind() == kind::BITVECTOR_SHL))
    {
      TNode p = in[0].getKind() == kind::BITVECTOR_ADD ? in[0] : in[1];
      TNode s = in[0].getKind() == kind::BITVECTOR_ADD ? in[1] : in[0];

      if (p.getNumChildren() == 2 && p[0].getKind() == kind::BITVECTOR_SHL
          && p[1].getKind() == kind::BITVECTOR_SHL)
      {
        if (utils::isOne(s[0]) && utils::isOne(p[0][0])
            && utils::isOne(p[1][0]))
        {
          Node zero = utils::mkZero(utils::getSize(s));
          TNode b = p[0];
          TNode c = p[1];
          // (s : 1 << S) = (b : 1 << B) + (c : 1 << C)
          Node b_eq_0 = b.eqNode(zero);
          Node c_eq_0 = c.eqNode(zero);
          Node b_eq_c = b.eqNode(c);

          Node dis = NodeManager::currentNM()->mkNode(
              kind::OR, b_eq_0, c_eq_0, b_eq_c);
          Node imp = in.impNode(dis);
          learned << imp;
        }
      }
    }
  }

  d_internal->ppStaticLearn(in, learned);
}

Node TheoryBV::getValue(TNode node)
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

    if (cur.isConst())
    {
      d_modelCache[cur] = cur;
      continue;
    }

    Node value = d_internal->getValue(cur, false);
    if (value.isConst())
    {
      d_modelCache[cur] = value;
      continue;
    }

    if (Theory::isLeafOf(cur, theory::THEORY_BV))
    {
      value = d_internal->getValue(cur, true);
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

      std::unordered_map<Node, Node>::iterator iit;
      for (const TNode& child : cur)
      {
        iit = d_modelCache.find(child);
        Assert(iit != d_modelCache.end());
        Assert(iit->second.isConst());
        nb << iit->second;
      }
      it->second = rewrite(nb.constructNode());
    }
  } while (!visit.empty());

  auto it = d_modelCache.find(node);
  Assert(it != d_modelCache.end());
  return it->second;
}

TheoryBV::Statistics::Statistics(StatisticsRegistry& reg,
                                 const std::string& name)
    : d_solveSubstitutions(reg.registerInt(name + "NumSolveSubstitutions"))
{
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
