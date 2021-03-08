/*********************                                                        */
/*! \file theory_bv.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner, Andrew Reynolds, Martin Brain
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/bv/theory_bv.h"

#include "options/bv_options.h"
#include "options/smt_options.h"
#include "theory/bv/bv_solver_bitblast.h"
#include "theory/bv/bv_solver_lazy.h"
#include "theory/bv/bv_solver_simple.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/ee_setup_info.h"

namespace CVC4 {
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
      d_im(*this, d_state, nullptr, "theory::bv"),
      d_notify(d_im)
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
    ee->addFunctionKind(kind::BITVECTOR_PLUS, true);
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

TrustNode TheoryBV::expandDefinition(Node node)
{
  Debug("bitvector-expandDefinition")
      << "TheoryBV::expandDefinition(" << node << ")" << std::endl;

  Node ret;
  switch (node.getKind())
  {
    case kind::BITVECTOR_SDIV:
    case kind::BITVECTOR_SREM:
    case kind::BITVECTOR_SMOD:
      ret = TheoryBVRewriter::eliminateBVSDiv(node);
      break;

    default: break;
  }
  if (!ret.isNull() && node != ret)
  {
    return TrustNode::mkTrustRewrite(node, ret, nullptr);
  }
  return TrustNode::null();
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
  return d_internal->ppAssert(tin, outSubstitutions);
}

TrustNode TheoryBV::ppRewrite(TNode t)
{
  // first, see if we need to expand definitions
  TrustNode texp = expandDefinition(t);
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

void TheoryBV::ppStaticLearn(TNode in, NodeBuilder<>& learned)
{
  d_internal->ppStaticLearn(in, learned);
}

bool TheoryBV::applyAbstraction(const std::vector<Node>& assertions,
                                std::vector<Node>& new_assertions)
{
  return d_internal->applyAbstraction(assertions, new_assertions);
}

}  // namespace bv
}  // namespace theory
}  // namespace CVC4
