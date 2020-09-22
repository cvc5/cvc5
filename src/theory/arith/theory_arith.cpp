/*********************                                                        */
/*! \file theory_arith.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Dejan Jovanovic
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
      d_nonlinearExtension(nullptr)
{
  smtStatisticsRegistry()->registerStat(&d_ppRewriteTimer);

  // indicate we are using the theory state object
  d_theoryState = &d_astate;
}

TheoryArith::~TheoryArith(){
  smtStatisticsRegistry()->unregisterStat(&d_ppRewriteTimer);
  delete d_internal;
}

TheoryRewriter* TheoryArith::getTheoryRewriter()
{
  return d_internal->getTheoryRewriter();
}

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
        new nl::NonlinearExtension(*this, d_equalityEngine));
  }
  // finish initialize internally
  d_internal->finishInit();
}

void TheoryArith::preRegisterTerm(TNode n) { d_internal->preRegisterTerm(n); }

TrustNode TheoryArith::expandDefinition(Node node)
{
  return d_internal->expandDefinition(node);
}

void TheoryArith::notifySharedTerm(TNode n) { d_internal->addSharedTerm(n); }

TrustNode TheoryArith::ppRewrite(TNode atom)
{
  CodeTimer timer(d_ppRewriteTimer, /* allow_reentrant = */ true);
  return d_internal->ppRewrite(atom);
}

Theory::PPAssertStatus TheoryArith::ppAssert(TNode in, SubstitutionMap& outSubstitutions) {
  return d_internal->ppAssert(in, outSubstitutions);
}

void TheoryArith::ppStaticLearn(TNode n, NodeBuilder<>& learned) {
  d_internal->ppStaticLearn(n, learned);
}

void TheoryArith::check(Effort effortLevel){
  getOutputChannel().spendResource(ResourceManager::Resource::TheoryCheckStep);
  d_internal->check(effortLevel);
}

bool TheoryArith::needsCheckLastEffort() {
  return d_internal->needsCheckLastEffort();
}

TrustNode TheoryArith::explain(TNode n)
{
  Node exp = d_internal->explain(n);
  return TrustNode::mkTrustPropExp(n, exp, nullptr);
}

void TheoryArith::propagate(Effort e) {
  d_internal->propagate(e);
}
bool TheoryArith::collectModelInfo(TheoryModel* m)
{
  std::set<Node> termSet;
  // Work out which variables are needed
  const std::set<Kind>& irrKinds = m->getIrrelevantKinds();
  computeAssertedTerms(termSet, irrKinds);
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
    Assert(p.second.isConst());
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

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
