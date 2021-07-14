/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arithmetic theory.
 */

#include "theory/arith/theory_arith.h"

#include "options/smt_options.h"
#include "proof/proof_checker.h"
#include "proof/proof_rule.h"
#include "smt/smt_statistics_registry.h"
#include "theory/arith/arith_rewriter.h"
#include "theory/arith/infer_bounds.h"
#include "theory/arith/nl/nonlinear_extension.h"
#include "theory/arith/theory_arith_private.h"
#include "theory/ext_theory.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"

using namespace std;
using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace arith {

TheoryArith::TheoryArith(context::Context* c,
                         context::UserContext* u,
                         OutputChannel& out,
                         Valuation valuation,
                         const LogicInfo& logicInfo,
                         ProofNodeManager* pnm)
    : Theory(THEORY_ARITH, c, u, out, valuation, logicInfo, pnm),
      d_ppRewriteTimer(smtStatisticsRegistry().registerTimer(
          "theory::arith::ppRewriteTimer")),
      d_astate(c, u, valuation),
      d_im(*this, d_astate, pnm),
      d_ppre(c, pnm),
      d_bab(d_astate, d_im, d_ppre, pnm),
      d_internal(new TheoryArithPrivate(*this, c, u, d_bab, pnm)),
      d_nonlinearExtension(nullptr),
      d_opElim(pnm, logicInfo),
      d_arithPreproc(d_astate, d_im, pnm, d_opElim),
      d_rewriter(d_opElim)
{
  // currently a cyclic dependency to TheoryArithPrivate
  d_astate.setParent(d_internal);
  // indicate we are using the theory state object and inference manager
  d_theoryState = &d_astate;
  d_inferManager = &d_im;
}

TheoryArith::~TheoryArith(){
  delete d_internal;
}

TheoryRewriter* TheoryArith::getTheoryRewriter() { return &d_rewriter; }

ProofRuleChecker* TheoryArith::getProofChecker()
{
  return d_internal->getProofChecker();
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

void TheoryArith::notifySharedTerm(TNode n) { d_internal->notifySharedTerm(n); }

TrustNode TheoryArith::ppRewrite(TNode atom, std::vector<SkolemLemma>& lems)
{
  CodeTimer timer(d_ppRewriteTimer, /* allow_reentrant = */ true);
  Debug("arith::preprocess") << "arith::preprocess() : " << atom << endl;

  if (atom.getKind() == kind::EQUAL)
  {
    return d_ppre.ppRewriteEq(atom);
  }
  Assert(Theory::theoryOf(atom) == THEORY_ARITH);
  // Eliminate operators. Notice we must do this here since other
  // theories may generate lemmas that involve non-standard operators. For
  // example, quantifier instantiation may use TO_INTEGER terms; SyGuS may
  // introduce non-standard arithmetic terms appearing in grammars.
  // call eliminate operators. In contrast to expandDefinitions, we eliminate
  // *all* extended arithmetic operators here, including total ones.
  return d_arithPreproc.eliminate(atom, lems, false);
}

Theory::PPAssertStatus TheoryArith::ppAssert(
    TrustNode tin, TrustSubstitutionMap& outSubstitutions)
{
  return d_internal->ppAssert(tin, outSubstitutions);
}

void TheoryArith::ppStaticLearn(TNode n, NodeBuilder& learned)
{
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
      d_im.setIncomplete(IncompleteId::ARITH_NL_DISABLED);
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
  // Double check that the model from the linear solver respects integer types,
  // if it does not, add a branch and bound lemma. This typically should never
  // be necessary, but is needed in rare cases.
  bool addedLemma = false;
  bool badAssignment = false;
  for (const std::pair<const Node, Node>& p : arithModel)
  {
    if (p.first.getType().isInteger() && !p.second.getType().isInteger())
    {
      Assert(false) << "TheoryArithPrivate generated a bad model value for "
                       "integer variable "
                    << p.first << " : " << p.second;
      // must branch and bound
      TrustNode lem =
          d_bab.branchIntegerVariable(p.first, p.second.getConst<Rational>());
      if (d_im.trustedLemma(lem, InferenceId::ARITH_BB_LEMMA))
      {
        addedLemma = true;
      }
      badAssignment = true;
    }
  }
  if (addedLemma)
  {
    // we had to add a branch and bound lemma since the linear solver assigned
    // a non-integer value to an integer variable.
    return false;
  }
  // this would imply that linear arithmetic's model failed to satisfy a branch
  // and bound lemma
  AlwaysAssert(!badAssignment)
      << "Bad assignment from TheoryArithPrivate::collectModelValues, and no "
         "branching lemma was sent";

  // if non-linear is enabled, intercept the model, which may repair its values
  if (d_nonlinearExtension != nullptr)
  {
    // Non-linear may repair values to satisfy non-linear constraints (see
    // documentation for NonlinearExtension::interceptModel).
    d_nonlinearExtension->interceptModel(arithModel, termSet);
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
      bool added = d_im.lemma(lem, InferenceId::ARITH_SPLIT_FOR_NL_MODEL);
      AlwaysAssert(added) << "The lemma was already in cache. Probably there is something wrong with theory combination...";
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
  return d_im.getProofEqEngine();
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5
