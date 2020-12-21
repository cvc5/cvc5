/*********************                                                        */
/*! \file theory_arith.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Alex Ozdemir
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/arith/theory_arith.h"

#include "options/prop_options.h"
#include "options/smt_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/arith/arith_rewriter.h"
#include "theory/arith/infer_bounds.h"
#include "theory/arith/nl/nonlinear_extension.h"
#include "theory/arith/theory_arith_private.h"
#include "theory/ext_theory.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {

TheoryArith::TheoryArith(context::Context* c,
                         context::UserContext* u,
                         OutputChannel& out,
                         Valuation valuation,
                         const LogicInfo& logicInfo,
                         ProofNodeManager* pnm)
    : Theory(THEORY_ARITH, c, u, out, valuation, logicInfo, pnm),
      d_internal(
          new TheoryArithPrivate(*this, c, u, out, valuation, logicInfo, pnm)),
      d_ppRewriteTimer("theory::arith::ppRewriteTimer"),
      d_astate(*d_internal, c, u, valuation),
      d_inferenceManager(*this, d_astate, pnm),
      d_nonlinearExtension(nullptr),
      d_arithPreproc(d_astate, d_inferenceManager, pnm, logicInfo)
{
  smtStatisticsRegistry()->registerStat(&d_ppRewriteTimer);

  // indicate we are using the theory state object and inference manager
  d_theoryState = &d_astate;
  d_inferManager = &d_inferenceManager;
}

TheoryArith::~TheoryArith(){
  smtStatisticsRegistry()->unregisterStat(&d_ppRewriteTimer);
  delete d_internal;
}

TheoryRewriter* TheoryArith::getTheoryRewriter() { return &d_rewriter; }

bool TheoryArith::needsEqualityEngine(EeSetupInfo& esi)
{
  return d_internal->needsEqualityEngine(esi);
}
void TheoryArith::finishInit()
{
  if (getLogicInfo().isTheoryEnabled(THEORY_ARITH)
      && getLogicInfo().areTranscendentalsUsed())
  {
    // witness is used to eliminate square root
    d_valuation.setUnevaluatedKind(kind::WITNESS);
    // we only need to add the operators that are not syntax sugar
    d_valuation.setUnevaluatedKind(kind::EXPONENTIAL);
    d_valuation.setUnevaluatedKind(kind::SINE);
    d_valuation.setUnevaluatedKind(kind::PI);
  }
  // only need to create nonlinear extension if non-linear logic
  const LogicInfo& logicInfo = getLogicInfo();
  if (logicInfo.isTheoryEnabled(THEORY_ARITH) && !logicInfo.isLinear())
  {
    d_nonlinearExtension.reset(
        new nl::NonlinearExtension(*this, d_astate, d_equalityEngine, d_pnm));
  }
  // finish initialize internally
  d_internal->finishInit();
}

void TheoryArith::preRegisterTerm(TNode n)
{
  if (d_nonlinearExtension != nullptr)
  {
    d_nonlinearExtension->preRegisterTerm(n);
  }
  d_internal->preRegisterTerm(n);
}

TrustNode TheoryArith::expandDefinition(Node node)
{
  // call eliminate operators, to eliminate partial operators only
  return d_arithPreproc.eliminate(node, true);
}

void TheoryArith::notifySharedTerm(TNode n) { d_internal->notifySharedTerm(n); }

TrustNode TheoryArith::ppRewrite(TNode n)
{
  CodeTimer timer(d_ppRewriteTimer, /* allow_reentrant = */ true);
  Debug("arith::preprocess") << "arith::preprocess() : " << n << endl;
  Assert(Theory::theoryOf(n) == THEORY_ARITH);
  // Eliminate operators recursively. Notice we must do this here since other
  // theories may generate lemmas that involve non-standard operators. For
  // example, quantifier instantiation may use TO_INTEGER terms; SyGuS may
  // introduce non-standard arithmetic terms appearing in grammars.
  // call eliminate operators. In contrast to expandDefinitions, we eliminate
  // *all* extended arithmetic operators here, including total ones.
  return d_arithPreproc.eliminate(n, false);
}

Theory::PPAssertStatus TheoryArith::ppAssert(
    TrustNode tin, TrustSubstitutionMap& outSubstitutions)
{
  return d_internal->ppAssert(tin, outSubstitutions);
}

void TheoryArith::ppStaticLearn(TNode n, NodeBuilder<>& learned) {
  d_internal->ppStaticLearn(n, learned);
}

bool TheoryArith::preCheck(Effort level)
{
  Trace("arith-check") << "TheoryArith::preCheck " << level << std::endl;
  return d_internal->preCheck(level);
}

void TheoryArith::postCheck(Effort level)
{
  Trace("arith-check") << "TheoryArith::postCheck " << level << std::endl;
  // check with the non-linear solver at last call
  if (level == Theory::EFFORT_LAST_CALL)
  {
    if (d_nonlinearExtension != nullptr)
    {
      d_nonlinearExtension->check(level);
    }
    return;
  }
  // otherwise, check with the linear solver
  if (d_internal->postCheck(level))
  {
    // linear solver emitted a conflict or lemma, return
    return;
  }

  if (Theory::fullEffort(level))
  {
    if (d_nonlinearExtension != nullptr)
    {
      d_nonlinearExtension->check(level);
    }
    else if (d_internal->foundNonlinear())
    {
      // set incomplete
      d_inferenceManager.setIncomplete();
    }
  }
}

bool TheoryArith::preNotifyFact(
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  Trace("arith-check") << "TheoryArith::preNotifyFact: " << fact
                       << ", isPrereg=" << isPrereg
                       << ", isInternal=" << isInternal << std::endl;
  d_internal->preNotifyFact(atom, pol, fact);
  // We do not assert to the equality engine of arithmetic in the standard way,
  // hence we return "true" to indicate we are finished with this fact.
  return true;
}

bool TheoryArith::needsCheckLastEffort() {
  if (d_nonlinearExtension != nullptr)
  {
    return d_nonlinearExtension->needsCheckLastEffort();
  }
  return false;
}

TrustNode TheoryArith::explain(TNode n) { return d_internal->explain(n); }

void TheoryArith::propagate(Effort e) {
  d_internal->propagate(e);
}

bool TheoryArith::collectModelInfo(TheoryModel* m,
                                   const std::set<Node>& termSet)
{
  // this overrides behavior to not assert equality engine
  return collectModelValues(m, termSet);
}

bool TheoryArith::collectModelValues(TheoryModel* m,
                                     const std::set<Node>& termSet)
{
  // get the model from the linear solver
  std::map<Node, Node> arithModel;
  d_internal->collectModelValues(termSet, arithModel);
  // if non-linear is enabled, intercept the model, which may repair its values
  if (d_nonlinearExtension != nullptr)
  {
    // Non-linear may repair values to satisfy non-linear constraints (see
    // documentation for NonlinearExtension::interceptModel).
    d_nonlinearExtension->interceptModel(arithModel);
  }
  // We are now ready to assert the model.
  for (const std::pair<const Node, Node>& p : arithModel)
  {
    // maps to constant of comparable type
    Assert(p.first.getType().isComparableTo(p.second.getType()));
    if (m->assertEquality(p.first, p.second, true))
    {
      continue;
    }
    // If we failed to assert an equality, it is likely due to theory
    // combination, namely the repaired model for non-linear changed
    // an equality status that was agreed upon by both (linear) arithmetic
    // and another theory. In this case, we must add a lemma, or otherwise
    // we would terminate with an invalid model. Thus, we add a splitting
    // lemma of the form ( x = v V x != v ) where v is the model value
    // assigned by the non-linear solver to x.
    if (d_nonlinearExtension != nullptr)
    {
      Node eq = p.first.eqNode(p.second);
      Node lem = NodeManager::currentNM()->mkNode(kind::OR, eq, eq.negate());
      d_out->lemma(lem);
    }
    return false;
  }
  return true;
}

void TheoryArith::notifyRestart(){
  d_internal->notifyRestart();
}

void TheoryArith::presolve(){
  d_internal->presolve();
  if (d_nonlinearExtension != nullptr)
  {
    d_nonlinearExtension->presolve();
  }
}

EqualityStatus TheoryArith::getEqualityStatus(TNode a, TNode b) {
  return d_internal->getEqualityStatus(a,b);
}

Node TheoryArith::getModelValue(TNode var) {
  return d_internal->getModelValue( var );
}

std::pair<bool, Node> TheoryArith::entailmentCheck(TNode lit)
{
  ArithEntailmentCheckParameters def;
  def.addLookupRowSumAlgorithms();
  ArithEntailmentCheckSideEffects ase;
  std::pair<bool, Node> res = d_internal->entailmentCheck(lit, def, ase);
  return res;
}
eq::ProofEqEngine* TheoryArith::getProofEqEngine()
{
  return d_inferenceManager.getProofEqEngine();
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
