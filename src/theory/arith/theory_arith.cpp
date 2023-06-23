/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arithmetic theory.
 */

#include "theory/arith/theory_arith.h"

#include "options/smt_options.h"
#include "printer/smt2/smt2_printer.h"
#include "proof/proof_checker.h"
#include "proof/proof_rule.h"
#include "smt/logic_exception.h"
#include "theory/arith/arith_evaluator.h"
#include "theory/arith/arith_rewriter.h"
#include "theory/arith/equality_solver.h"
#include "theory/arith/linear/theory_arith_private.h"
#include "theory/arith/nl/nonlinear_extension.h"
#include "theory/ext_theory.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"
#include "util/cocoa_globals.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {

TheoryArith::TheoryArith(Env& env, OutputChannel& out, Valuation valuation)
    : Theory(THEORY_ARITH, env, out, valuation),
      d_ppRewriteTimer(
          statisticsRegistry().registerTimer("theory::arith::ppRewriteTimer")),
      d_astate(env, valuation),
      d_im(env, *this, d_astate),
      d_ppre(d_env),
      d_bab(env, d_astate, d_im, d_ppre),
      d_eqSolver(nullptr),
      d_internal(new linear::TheoryArithPrivate(*this, env, d_bab)),
      d_nonlinearExtension(nullptr),
      d_opElim(d_env),
      d_arithPreproc(env, d_im, d_pnm, d_opElim),
      d_rewriter(d_opElim),
      d_arithModelCacheSet(false),
      d_checker()
{
#ifdef CVC5_USE_COCOA
  // must be initialized before using CoCoA.
  initCocoaGlobalManager();
#endif /* CVC5_USE_COCOA */
  // indicate we are using the theory state object and inference manager
  d_theoryState = &d_astate;
  d_inferManager = &d_im;

  // construct the equality solver
  d_eqSolver.reset(new EqualitySolver(env, d_astate, d_im));
}

TheoryArith::~TheoryArith(){
  delete d_internal;
}

TheoryRewriter* TheoryArith::getTheoryRewriter() { return &d_rewriter; }

ProofRuleChecker* TheoryArith::getProofChecker() { return &d_checker; }

bool TheoryArith::needsEqualityEngine(EeSetupInfo& esi)
{
  // if the equality solver is enabled, then it is responsible for setting
  // up the equality engine
  return d_eqSolver->needsEqualityEngine(esi);
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
    d_nonlinearExtension.reset(new nl::NonlinearExtension(d_env, *this));
  }
  d_eqSolver->finishInit();
  // finish initialize in the old linear solver
  d_internal->finishInit();

  // Set the congruence manager on the equality solver. If the congruence
  // manager exists, it is responsible for managing the notifications from
  // the equality engine, which the equality solver forwards to it.
  d_eqSolver->setCongruenceManager(d_internal->getCongruenceManager());
}

void TheoryArith::preRegisterTerm(TNode n)
{
  // handle logic exceptions
  Kind k = n.getKind();
  bool isTransKind = isTranscendentalKind(k);
  // note that we don't throw an exception for non-linear multiplication in
  // linear logics, since this is caught in the linear solver with a more
  // informative error message
  if (isTransKind || k == IAND || k == POW2)
  {
    if (d_nonlinearExtension == nullptr)
    {
      std::stringstream ss;
      ss << "Term of kind " << k
         << " requires the logic to include non-linear arithmetic";
      throw LogicException(ss.str());
    }
    // logic exceptions based on the configuration of nl-ext: if we are a
    // transcendental function, we require nl-ext=full.
    if (isTransKind)
    {
      if (options().arith.nlExt != options::NlExtMode::FULL)
      {
        std::stringstream ss;
        ss << "Term of kind " << k
           << " requires nl-ext mode to be set to value 'full'";
        throw LogicException(ss.str());
      }
    }
    if (options().arith.nlCov && !options().arith.nlCovForce)
    {
      std::stringstream ss;
      ss << "Term of kind " << k
         << " is not compatible with using the coverings-based solver. If "
            "you know what you are doing, "
            "you can try --nl-cov-force, but expect crashes or incorrect "
            "results.";
      throw LogicException(ss.str());
    }
  }
  if (d_nonlinearExtension != nullptr)
  {
    d_nonlinearExtension->preRegisterTerm(n);
  }
  d_internal->preRegisterTerm(n);
}

void TheoryArith::notifySharedTerm(TNode n)
{
  n = n.getKind() == kind::TO_REAL ? n[0] : n;
  d_internal->notifySharedTerm(n);
}

TrustNode TheoryArith::ppRewrite(TNode atom, std::vector<SkolemLemma>& lems)
{
  CodeTimer timer(d_ppRewriteTimer, /* allow_reentrant = */ true);
  Trace("arith::preprocess") << "arith::ppRewrite() : " << atom << endl;
  Assert(d_env.theoryOf(atom) == THEORY_ARITH);
  // Eliminate operators. Notice we must do this here since other
  // theories may generate lemmas that involve non-standard operators. For
  // example, quantifier instantiation may use TO_INTEGER terms; SyGuS may
  // introduce non-standard arithmetic terms appearing in grammars.
  // call eliminate operators. In contrast to expandDefinitions, we eliminate
  // *all* extended arithmetic operators here, including total ones.
  return d_arithPreproc.eliminate(atom, lems, false);
}

TrustNode TheoryArith::ppStaticRewrite(TNode atom)
{
  Trace("arith::preprocess") << "arith::ppStaticRewrite() : " << atom << endl;
  Kind k = atom.getKind();
  if (k == kind::EQUAL)
  {
    return d_ppre.ppRewriteEq(atom);
  }
  else if (k == kind::GEQ)
  {
    // try to eliminate bv2nat from inequalities
    Node atomr = ArithRewriter::rewriteIneqToBv(atom);
    if (atomr != atom)
    {
      return TrustNode::mkTrustRewrite(atom, atomr);
    }
  }
  return TrustNode::null();
}

Theory::PPAssertStatus TheoryArith::ppAssert(
    TrustNode tin, TrustSubstitutionMap& outSubstitutions)
{
  return d_internal->ppAssert(tin, outSubstitutions);
}

void TheoryArith::ppStaticLearn(TNode n, NodeBuilder& learned)
{
  if (options().arith.arithStaticLearning)
  {
    d_internal->ppStaticLearn(n, learned);
  }
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
  if (Theory::fullEffort(level))
  {
    // Make sure we don't have old lemmas floating around. This can happen if we
    // didn't actually reach a last call effort check, but backtracked for some
    // other reason. In such a case, these lemmas are likely to be irrelevant
    // and possibly even harmful. If we produce proofs, their proofs have most
    // likely been deallocated already as well.
    d_im.clearPending();
    d_im.clearWaitingLemmas();
  }
  // check with the non-linear solver at last call
  if (level == Theory::EFFORT_LAST_CALL)
  {
    // If we computed lemmas in the last FULL_EFFORT check, send them now.
    if (d_im.hasPendingLemma())
    {
      d_im.doPendingFacts();
      d_im.doPendingLemmas();
      d_im.doPendingPhaseRequirements();
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
    d_arithModelCacheIllTyped.clear();
    d_arithModelCacheSubs.clear();
    d_arithModelCacheSet = false;
    std::set<Node> termSet;
    if (d_nonlinearExtension != nullptr)
    {
      updateModelCache(termSet);
      // Check at full effort. This may either send lemmas or otherwise
      // buffer lemmas that we send at last call.
      d_nonlinearExtension->checkFullEffort(d_arithModelCache, termSet);
      // if we already sent a lemma, we are done
      if (d_im.hasSent())
      {
        return;
      }
    }
    else if (d_internal->foundNonlinear())
    {
      // set incomplete
      d_im.setModelUnsound(IncompleteId::ARITH_NL_DISABLED);
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
    // Now, finalize the model cache, which constructs a substitution to be
    // used for getEqualityStatus.
    finalizeModelCache();
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
  if (options().arith.arithEqSolver)
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
  // if the equality solver has an explanation for it, use it
  TrustNode texp = d_eqSolver->explain(n);
  if (!texp.isNull())
  {
    return texp;
  }
  return d_internal->explain(n);
}

void TheoryArith::propagate(Effort e) {
  d_internal->propagate(e);
}

bool TheoryArith::collectModelInfo(TheoryModel* m,
                                   const std::set<Node>& termSet)
{
  // If we have a buffered lemma (from the non-linear extension), then we
  // do not assert model values, since those values are likely incorrect.
  // Moreover, the model does not need to satisfy the assertions, so
  // arbitrary values can be used for arithmetic terms. Hence, we do
  // nothing here. The buffered lemmas will be sent immediately
  // at LAST_CALL effort (see postCheck).
  if (d_im.hasPendingLemma())
  {
    return true;
  }
  // this overrides behavior to not assert equality engine
  return collectModelValues(m, termSet);
}

bool TheoryArith::collectModelValues(TheoryModel* m,
                                     const std::set<Node>& termSet)
{
  if (TraceIsOn("arith::model"))
  {
    Trace("arith::model") << "arithmetic model after pruning" << std::endl;
    for (const auto& p : d_arithModelCache)
    {
      Trace("arith::model") << "\t" << p.first << " -> " << p.second << std::endl;
    }
  }

  updateModelCacheInternal(termSet);

  // We are now ready to assert the model.
  for (const std::pair<const Node, Node>& p : d_arithModelCache)
  {
    if (termSet.find(p.first) == termSet.end())
    {
      continue;
    }
    // do not assert non-leafs e.g. non-linear multiplication terms,
    // transcendental functions, etc.
    if (!Theory::isLeafOf(p.first, TheoryId::THEORY_ARITH))
    {
      continue;
    }
    // maps to constant of same type
    Assert(p.first.getType() == p.second.getType())
        << "Bad type : " << p.first << " -> " << p.second;
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
  Trace("arith-eq-status") << "TheoryArith::getEqualityStatus(" << a << ", " << b << ")" << std::endl;
  if (a == b)
  {
    Trace("arith-eq-status") << "...return (trivial) true" << std::endl;
    return EQUALITY_TRUE_IN_MODEL;
  }
  if (d_arithModelCache.empty())
  {
    EqualityStatus es = d_internal->getEqualityStatus(a, b);
    Trace("arith-eq-status") << "...return (from linear) " << es << std::endl;
    return es;
  }
  Trace("arith-eq-status") << "Evaluate under " << d_arithModelCacheSubs.d_vars << " / "
                 << d_arithModelCacheSubs.d_subs << std::endl;
  Node diff = NodeManager::currentNM()->mkNode(Kind::SUB, a, b);
  std::optional<bool> isZero =
      isExpressionZero(d_env, diff, d_arithModelCacheSubs);
  if (isZero)
  {
    EqualityStatus es =
        *isZero ? EQUALITY_TRUE_IN_MODEL : EQUALITY_FALSE_IN_MODEL;
    Trace("arith-eq-status") << "...return (from evaluate) " << es << std::endl;
    return es;
  }
  Trace("arith-eq-status") << "...return unknown" << std::endl;
  return EQUALITY_UNKNOWN;
}

Node TheoryArith::getCandidateModelValue(TNode var)
{
  var = var.getKind() == kind::TO_REAL ? var[0] : var;
  std::map<Node, Node>::iterator it = d_arithModelCache.find(var);
  if (it != d_arithModelCache.end())
  {
    return it->second;
  }
  return d_internal->getCandidateModelValue(var);
}

std::pair<bool, Node> TheoryArith::entailmentCheck(TNode lit)
{
  return d_internal->entailmentCheck(lit);
}

eq::ProofEqEngine* TheoryArith::getProofEqEngine()
{
  return d_im.getProofEqEngine();
}

void TheoryArith::updateModelCache(std::set<Node>& termSet)
{
  if (!d_arithModelCacheSet)
  {
    collectAssertedTermsForModel(termSet);
    updateModelCacheInternal(termSet);
  }
}
void TheoryArith::updateModelCacheInternal(const std::set<Node>& termSet)
{
  if (!d_arithModelCacheSet)
  {
    d_arithModelCacheSet = true;
    d_internal->collectModelValues(
        termSet, d_arithModelCache, d_arithModelCacheIllTyped);
  }
}

void TheoryArith::finalizeModelCache()
{
  // make into substitution
  for (const auto& [node, repl] : d_arithModelCache)
  {
    Assert(repl.getType().isRealOrInt());
    // we only keep the domain of the substitution that is for leafs of
    // arithmetic; otherwise we are using the value of the abstraction of
    // non-linear term from the linear solver, which can be incorrect.
    if (Theory::isLeafOf(node, TheoryId::THEORY_ARITH))
    {
      d_arithModelCacheSubs.add(node, repl);
    }
  }
}

bool TheoryArith::sanityCheckIntegerModel()
{
  // Double check that the model from the linear solver respects integer types,
  // if it does not, add a branch and bound lemma. This typically should never
  // be necessary, but is needed in rare cases.
  if (Configuration::isAssertionBuild())
  {
    for (CVC5_UNUSED const auto& p : d_arithModelCache)
    {
      Assert(p.first.getType() == p.second.getType())
          << "Bad type: " << p.first << " -> " << p.second;
    }
  }
  bool addedLemma = false;
  bool badAssignment = false;
  Trace("arith-check") << "model:" << std::endl;
  for (const auto& p : d_arithModelCacheIllTyped)
  {
    Trace("arith-check") << p.first << " -> " << p.second << std::endl;
    Assert(p.first.getType().isInteger() && !p.second.getType().isInteger());
    warning() << "TheoryArithPrivate generated a bad model value for "
                 "integer variable "
              << p.first << " : " << p.second << std::endl;
    // must branch and bound
    std::vector<TrustNode> lems =
        d_bab.branchIntegerVariable(p.first, p.second.getConst<Rational>());
    for (const TrustNode& lem : lems)
    {
      if (d_im.trustedLemma(lem, InferenceId::ARITH_BB_LEMMA))
      {
        addedLemma = true;
      }
    }
    badAssignment = true;
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
}  // namespace cvc5::internal
