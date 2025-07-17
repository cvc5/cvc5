/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Theory of bit-vectors.
 */

#include "theory/bv/theory_bv.h"

#include "expr/skolem_manager.h"
#include "options/bv_options.h"
#include "options/smt_options.h"
#include "proof/proof_checker.h"
#include "theory/bv/bv_solver_bitblast.h"
#include "theory/bv/bv_solver_bitblast_internal.h"
#include "theory/bv/theory_bv_rewrite_rules_normalization.h"
#include "theory/bv/theory_bv_rewrite_rules_simplification.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/ee_setup_info.h"
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
      d_ppAssert(env, valuation),
      d_rewriter(nodeManager()),
      d_state(env, valuation),
      d_im(env, *this, d_state, "theory::bv::"),
      d_notify(d_im),
      d_invalidateModelCache(context(), true),
      d_stats(statisticsRegistry(), "theory::bv::"),
      d_checker(nodeManager())
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

ProofRuleChecker* TheoryBV::getProofChecker() { return &d_checker; }

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
  getValuation().setSemiEvaluatedKind(Kind::BITVECTOR_ACKERMANNIZE_UDIV);
  getValuation().setSemiEvaluatedKind(Kind::BITVECTOR_ACKERMANNIZE_UREM);
  d_internal->finishInit();

  eq::EqualityEngine* ee = getEqualityEngine();
  if (ee)
  {
    bool eagerEval = options().bv.bvEagerEval;
    // The kinds we are treating as function application in congruence
    ee->addFunctionKind(Kind::BITVECTOR_CONCAT, eagerEval);
    //    ee->addFunctionKind(Kind::BITVECTOR_AND);
    //    ee->addFunctionKind(Kind::BITVECTOR_OR);
    //    ee->addFunctionKind(Kind::BITVECTOR_XOR);
    //    ee->addFunctionKind(Kind::BITVECTOR_NOT);
    //    ee->addFunctionKind(Kind::BITVECTOR_NAND);
    //    ee->addFunctionKind(Kind::BITVECTOR_NOR);
    //    ee->addFunctionKind(Kind::BITVECTOR_XNOR);
    //    ee->addFunctionKind(Kind::BITVECTOR_COMP);
    ee->addFunctionKind(Kind::BITVECTOR_MULT, eagerEval);
    ee->addFunctionKind(Kind::BITVECTOR_ADD, eagerEval);
    ee->addFunctionKind(Kind::BITVECTOR_EXTRACT, eagerEval);
    //    ee->addFunctionKind(Kind::BITVECTOR_SUB);
    //    ee->addFunctionKind(Kind::BITVECTOR_NEG);
    //    ee->addFunctionKind(Kind::BITVECTOR_UDIV);
    //    ee->addFunctionKind(Kind::BITVECTOR_UREM);
    //    ee->addFunctionKind(Kind::BITVECTOR_SDIV);
    //    ee->addFunctionKind(Kind::BITVECTOR_SREM);
    //    ee->addFunctionKind(Kind::BITVECTOR_SMOD);
    //    ee->addFunctionKind(Kind::BITVECTOR_SHL);
    //    ee->addFunctionKind(Kind::BITVECTOR_LSHR);
    //    ee->addFunctionKind(Kind::BITVECTOR_ASHR);
    //    ee->addFunctionKind(Kind::BITVECTOR_ULT);
    //    ee->addFunctionKind(Kind::BITVECTOR_ULE);
    //    ee->addFunctionKind(Kind::BITVECTOR_UGT);
    //    ee->addFunctionKind(Kind::BITVECTOR_UGE);
    //    ee->addFunctionKind(Kind::BITVECTOR_SLT);
    //    ee->addFunctionKind(Kind::BITVECTOR_SLE);
    //    ee->addFunctionKind(Kind::BITVECTOR_SGT);
    //    ee->addFunctionKind(Kind::BITVECTOR_SGE);
  }
}

void TheoryBV::preRegisterTerm(TNode node)
{
  d_internal->preRegisterTerm(node);

  eq::EqualityEngine* ee = getEqualityEngine();
  if (ee)
  {
    if (node.getKind() == Kind::EQUAL)
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

bool TheoryBV::ppAssert(TrustNode tin, TrustSubstitutionMap& outSubstitutions)
{
  Kind k = tin.getNode().getKind();
  if (k == Kind::EQUAL)
  {
    bool status = Theory::ppAssert(tin, outSubstitutions);
    if (status)
    {
      return status;
    }
    if (d_ppAssert.ppAssert(tin, outSubstitutions))
    {
      return true;
    }
  }
  return false;
}

TrustNode TheoryBV::ppRewrite(TNode t, std::vector<SkolemLemma>& lems)
{
  Trace("theory-bv-pp-rewrite") << "ppRewrite " << t << "\n";
  Node res = t;
  // useful on QF_BV/space/ndist
  if (RewriteRule<UltAddOne>::applies(t))
  {
    res = RewriteRule<UltAddOne>::run<false>(t);
  }
  // When int-blasting, it is better to handle most overflow operators
  // natively, rather than to eliminate them eagerly.
  if (options().smt.solveBVAsInt == options::SolveBVAsIntMode::OFF)
  {
    res = d_rewriter.eliminateOverflows(res);
  }

  Trace("theory-bv-pp-rewrite") << "to   " << res << "\n";
  if (res != t)
  {
    return TrustNode::mkTrustRewrite(t, res, nullptr);
  }

  return d_internal->ppRewrite(t);
}

TrustNode TheoryBV::ppStaticRewrite(TNode atom)
{
  Kind k = atom.getKind();
  if (k == Kind::EQUAL)
  {
    if (RewriteRule<SolveEq>::applies(atom))
    {
      Node res = RewriteRule<SolveEq>::run<false>(atom);
      if (res != atom)
      {
        return TrustNode::mkTrustRewrite(atom, res);
      }
    }
    if (options().bv.bitwiseEq && RewriteRule<BitwiseEq>::applies(atom))
    {
      Node res = RewriteRule<BitwiseEq>::run<false>(atom);
      if (res != atom)
      {
        return TrustNode::mkTrustRewrite(atom, res);
      }
    }
    // Useful for BV/2017-Preiner-scholl-smt08, but not for QF_BV
    if (options().bv.rwExtendEq)
    {
      Node res;
      if (RewriteRule<SignExtendEqConst>::applies(atom))
      {
        res = RewriteRule<SignExtendEqConst>::run<false>(atom);
      }
      else if (RewriteRule<ZeroExtendEqConst>::applies(atom))
      {
        res = RewriteRule<ZeroExtendEqConst>::run<false>(atom);
      }
      if (res != atom)
      {
        return TrustNode::mkTrustRewrite(atom, res);
      }
    }
  }
  return TrustNode::null();
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

void TheoryBV::ppStaticLearn(TNode in, std::vector<TrustNode>& learned)
{
  if (in.getKind() == Kind::EQUAL)
  {
    // Only useful in combination with --bv-intro-pow2 on
    // QF_BV/pspace/power2sum benchmarks.
    //
    // Matches for equality:
    //
    // (= (bvadd (bvshl 1 x) (bvshl 1 y)) (bvshl 1 z))
    //
    // and does case analysis on the sum of two power of twos.
    if ((in[0].getKind() == Kind::BITVECTOR_ADD
         && in[1].getKind() == Kind::BITVECTOR_SHL)
        || (in[1].getKind() == Kind::BITVECTOR_ADD
            && in[0].getKind() == Kind::BITVECTOR_SHL))
    {
      TNode p = in[0].getKind() == Kind::BITVECTOR_ADD ? in[0] : in[1];
      TNode s = in[0].getKind() == Kind::BITVECTOR_ADD ? in[1] : in[0];

      if (p.getNumChildren() == 2 && p[0].getKind() == Kind::BITVECTOR_SHL
          && p[1].getKind() == Kind::BITVECTOR_SHL)
      {
        if (utils::isOne(s[0]) && utils::isOne(p[0][0])
            && utils::isOne(p[1][0]))
        {
          Node zero = utils::mkZero(nodeManager(), utils::getSize(s));
          TNode b = p[0];
          TNode c = p[1];
          // (s : 1 << S) = (b : 1 << B) + (c : 1 << C)
          Node b_eq_0 = b.eqNode(zero);
          Node c_eq_0 = c.eqNode(zero);
          Node b_eq_c = b.eqNode(c);

          Node dis = nodeManager()->mkNode(Kind::OR, b_eq_0, c_eq_0, b_eq_c);
          Node imp = in.impNode(dis);
          TrustNode trn = TrustNode::mkTrustLemma(imp, nullptr);
          learned.emplace_back(trn);
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
      NodeBuilder nb(nodeManager(), cur.getKind());
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
