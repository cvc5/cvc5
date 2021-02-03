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
      d_ufDivByZero(),
      d_ufRemByZero(),
      d_rewriter(),
      d_state(c, u, valuation),
      d_inferMgr(*this, d_state, nullptr)
{
  switch (options::bvSolver())
  {
    case options::BVSolver::BITBLAST:
      d_internal.reset(new BVSolverBitblast(&d_state, d_inferMgr, pnm));
      break;

    case options::BVSolver::LAZY:
      d_internal.reset(new BVSolverLazy(*this, c, u, pnm, name));
      break;

    default:
      AlwaysAssert(options::bvSolver() == options::BVSolver::SIMPLE);
      d_internal.reset(new BVSolverSimple(&d_state, d_inferMgr, pnm));
  }
  d_theoryState = &d_state;
  d_inferManager = &d_inferMgr;
}

TheoryBV::~TheoryBV() {}

TheoryRewriter* TheoryBV::getTheoryRewriter() { return &d_rewriter; }

bool TheoryBV::needsEqualityEngine(EeSetupInfo& esi)
{
  return d_internal->needsEqualityEngine(esi);
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

Node TheoryBV::getUFDivByZero(Kind k, unsigned width)
{
  NodeManager* nm = NodeManager::currentNM();
  if (k == kind::BITVECTOR_UDIV)
  {
    if (d_ufDivByZero.find(width) == d_ufDivByZero.end())
    {
      // lazily create the function symbols
      std::ostringstream os;
      os << "BVUDivByZero_" << width;
      Node divByZero =
          nm->mkSkolem(os.str(),
                       nm->mkFunctionType(nm->mkBitVectorType(width),
                                          nm->mkBitVectorType(width)),
                       "partial bvudiv",
                       NodeManager::SKOLEM_EXACT_NAME);
      d_ufDivByZero[width] = divByZero;
    }
    return d_ufDivByZero[width];
  }
  else if (k == kind::BITVECTOR_UREM)
  {
    if (d_ufRemByZero.find(width) == d_ufRemByZero.end())
    {
      std::ostringstream os;
      os << "BVURemByZero_" << width;
      Node divByZero =
          nm->mkSkolem(os.str(),
                       nm->mkFunctionType(nm->mkBitVectorType(width),
                                          nm->mkBitVectorType(width)),
                       "partial bvurem",
                       NodeManager::SKOLEM_EXACT_NAME);
      d_ufRemByZero[width] = divByZero;
    }
    return d_ufRemByZero[width];
  }

  Unreachable();
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

    case kind::BITVECTOR_UDIV:
    case kind::BITVECTOR_UREM:
    {
      NodeManager* nm = NodeManager::currentNM();

      Kind kind = node.getKind() == kind::BITVECTOR_UDIV
                      ? kind::BITVECTOR_UDIV_TOTAL
                      : kind::BITVECTOR_UREM_TOTAL;
      ret = nm->mkNode(kind, node[0], node[1]);
      break;
    }
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
