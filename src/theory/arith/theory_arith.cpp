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
#include "theory/arith/arith_evaluator.h"
#include "theory/arith/arith_rewriter.h"
#include "theory/arith/equality_solver.h"
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

TheoryArith::TheoryArith(Env& env, OutputChannel& out, Valuation valuation)
    : Theory(THEORY_ARITH, env, out, valuation),
      d_ppRewriteTimer(
          statisticsRegistry().registerTimer("theory::arith::ppRewriteTimer")),
      d_astate(env, valuation),
      d_im(env, *this, d_astate),
      d_ppre(d_env),
      d_bab(env, d_astate, d_im, d_ppre, d_pnm),
      d_eqSolver(nullptr),
      d_internal(new TheoryArithPrivate(*this, env, d_bab)),
      d_nonlinearExtension(nullptr),
      d_opElim(d_env),
      d_arithPreproc(env, d_astate, d_im, d_pnm, d_opElim),
      d_rewriter(d_opElim),
      d_arithModelCacheSet(false)
{
  // currently a cyclic dependency to TheoryArithPrivate
  d_astate.setParent(d_internal);
  // indicate we are using the theory state object and inference manager
  d_theoryState = &d_astate;
  d_inferManager = &d_im;

  if (options().arith.arithEqSolver)
  {
    d_eqSolver.reset(new EqualitySolver(env, d_astate, d_im));
  }
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
  // if the equality solver is enabled, then it is responsible for setting
  // up the equality engine
  if (d_eqSolver != nullptr)
  {
    return d_eqSolver->needsEqualityEngine(esi);
  }
  // otherwise, the linear arithmetic solver is responsible for setting up
  // the equality engine
  return d_internal->needsEqualityEngine(esi);
}
void TheoryArith::finishInit()
{
  const LogicInfo& logic = logicInfo();
  if (logic.isTheoryEnabled(THEORY_ARITH) && logic.areTranscendentalsUsed())
  {
    // witness is used to eliminate square root
    d_valuation.setUnevaluatedKind(kind::WITNESS);
    // we only need to add the operators that are not syntax sugar
    d_valuation.setUnevaluatedKind(kind::EXPONENTIAL);
    d_valuation.setUnevaluatedKind(kind::SINE);
    d_valuation.setUnevaluatedKind(kind::PI);
  }
  // only need to create nonlinear extension if non-linear logic
  if (logic.isTheoryEnabled(THEORY_ARITH) && !logic.isLinear())
  {
    d_nonlinearExtension.reset(
        new nl::NonlinearExtension(d_env, *this, d_astate));
  }
  if (d_eqSolver != nullptr)
  {
    d_eqSolver->finishInit();
  }
  // finish initialize in the old linear solver
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
  Assert(d_env.theoryOf(atom) == THEORY_ARITH);
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
  d_im.reset();
  Trace("arith-check") << "TheoryArith::postCheck " << level << std::endl;
  // check with the non-linear solver at last call
  if (level == Theory::EFFORT_LAST_CALL)
  {
    if (d_nonlinearExtension != nullptr)
    {
      // If we computed lemmas in the last FULL_EFFORT check, send them now.
      if (d_im.hasPendingLemma())
      {
        d_im.doPendingFacts();
        d_im.doPendingLemmas();
        d_im.doPendingPhaseRequirements();
        return;
      }
    }
    return;
  }
  // otherwise, check with the linear solver
  if (d_internal->postCheck(level))
  {
    // linear solver emitted a conflict or lemma, return
    return;
  }
  if (d_im.hasSent())
  {
    return;
  }

  if (Theory::fullEffort(level))
  {
    d_arithModelCache.clear();
    d_arithModelCacheSet = false;
    std::set<Node> termSet;
    if (d_nonlinearExtension != nullptr)
    {
      updateModelCache(termSet);
      d_nonlinearExtension->checkFullEffort(d_arithModelCache, termSet);
    }
    else if (d_internal->foundNonlinear())
    {
      // set incomplete
      d_im.setIncomplete(IncompleteId::ARITH_NL_DISABLED);
    }
    // If we won't be doing a last call effort check (which implies that
    // models will be computed), we must sanity check the integer model
    // from the linear solver now. We also must update the model cache
    // if we did not do so above.
    if (d_nonlinearExtension == nullptr)
    {
      updateModelCache(termSet);
    }
    sanityCheckIntegerModel();
  }
}

bool TheoryArith::preNotifyFact(
    TNode atom, bool pol, TNode fact, bool isPrereg, bool isInternal)
{
  Trace("arith-check") << "TheoryArith::preNotifyFact: " << fact
                       << ", isPrereg=" << isPrereg
                       << ", isInternal=" << isInternal << std::endl;
  // We do not assert to the equality engine of arithmetic in the standard way,
  // hence we return "true" to indicate we are finished with this fact.
  bool ret = true;
  if (d_eqSolver != nullptr)
  {
    // the equality solver may indicate ret = false, after which the assertion
    // will be asserted to the equality engine in the default way.
    ret = d_eqSolver->preNotifyFact(atom, pol, fact, isPrereg, isInternal);
  }
  // we also always also notify the internal solver
  d_internal->preNotifyFact(atom, pol, fact);
  return ret;
}

bool TheoryArith::needsCheckLastEffort() {
  if (d_nonlinearExtension != nullptr)
  {
    return d_nonlinearExtension->hasNlTerms();
  }
  return false;
}

TrustNode TheoryArith::explain(TNode n)
{
  if (d_eqSolver != nullptr)
  {
    // if the equality solver has an explanation for it, use it
    TrustNode texp = d_eqSolver->explain(n);
    if (!texp.isNull())
    {
      return texp;
    }
  }
  return d_internal->explain(n);
}

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
  if (Trace.isOn("arith::model"))
  {
    Trace("arith::model") << "arithmetic model after pruning" << std::endl;
    for (const auto& p : d_arithModelCache)
    {
      Trace("arith::model") << "\t" << p.first << " -> " << p.second << std::endl;
    }
  }

  updateModelCache(termSet);

  // We are now ready to assert the model.
  for (const std::pair<const Node, Node>& p : d_arithModelCache)
  {
    if (termSet.find(p.first) == termSet.end())
    {
      continue;
    }
    // maps to constant of comparable type
    Assert(p.first.getType().isComparableTo(p.second.getType()));
    if (m->assertEquality(p.first, p.second, true))
    {
      continue;
    }
    Assert(false) << "A model equality could not be asserted: " << p.first
                        << " == " << p.second << std::endl;
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
}

EqualityStatus TheoryArith::getEqualityStatus(TNode a, TNode b) {
  Debug("arith") << "TheoryArith::getEqualityStatus(" << a << ", " << b << ")" << std::endl;
  if (a == b)
  {
    return EQUALITY_TRUE_IN_MODEL;
  }
  if (d_arithModelCache.empty())
  {
    return d_internal->getEqualityStatus(a,b);
  }
  Node diff = d_env.getNodeManager()->mkNode(Kind::SUB, a, b);
  std::optional<bool> isZero = isExpressionZero(d_env, diff, d_arithModelCache);
  if (isZero)
  {
    return *isZero ? EQUALITY_TRUE_IN_MODEL : EQUALITY_FALSE_IN_MODEL;
  }
  return EQUALITY_UNKNOWN;
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

void TheoryArith::updateModelCache(std::set<Node>& termSet)
{
  if (!d_arithModelCacheSet)
  {
    d_arithModelCacheSet = true;
    collectAssertedTerms(termSet);
    d_internal->collectModelValues(termSet, d_arithModelCache);
  }
}
void TheoryArith::updateModelCache(const std::set<Node>& termSet)
{
  if (!d_arithModelCacheSet)
  {
    d_arithModelCacheSet = true;
    d_internal->collectModelValues(termSet, d_arithModelCache);
  }
}
bool TheoryArith::sanityCheckIntegerModel()
{

    // Double check that the model from the linear solver respects integer types,
    // if it does not, add a branch and bound lemma. This typically should never
    // be necessary, but is needed in rare cases.
    bool addedLemma = false;
    bool badAssignment = false;
    Trace("arith-check") << "model:" << std::endl;
    for (const auto& p : d_arithModelCache)
    {
      Trace("arith-check") << p.first << " -> " << p.second << std::endl;
      if (p.first.getType().isInteger() && !p.second.getType().isInteger())
      {
        warning() << "TheoryArithPrivate generated a bad model value for "
                     "integer variable "
                  << p.first << " : " << p.second << std::endl;
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
      return true;
    }
    // this would imply that linear arithmetic's model failed to satisfy a branch
    // and bound lemma
    AlwaysAssert(!badAssignment)
        << "Bad assignment from TheoryArithPrivate::collectModelValues, and no "
          "branching lemma was sent";
    return false;
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5
