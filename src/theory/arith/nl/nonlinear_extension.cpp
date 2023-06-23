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
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "theory/arith/nl/nonlinear_extension.h"

#include "options/arith_options.h"
#include "options/smt_options.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/bound_inference.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_lemma_utils.h"
#include "theory/arith/theory_arith.h"
#include "theory/ext_theory.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

NonlinearExtension::NonlinearExtension(Env& env, TheoryArith& containing)
    : EnvObj(env),
      d_containing(containing),
      d_astate(*containing.getTheoryState()),
      d_im(containing.getInferenceManager()),
      d_stats(statisticsRegistry()),
      d_hasNlTerms(false),
      d_checkCounter(0),
      d_extTheoryCb(d_astate.getEqualityEngine()),
      d_extTheory(env, d_extTheoryCb, d_im),
      d_model(env),
      d_trSlv(d_env, d_astate, d_im, d_model),
      d_extState(d_env, d_im, d_model),
      d_factoringSlv(d_env, &d_extState),
      d_monomialBoundsSlv(d_env, &d_extState),
      d_monomialSlv(d_env, &d_extState),
      d_splitZeroSlv(d_env, &d_extState),
      d_tangentPlaneSlv(d_env, &d_extState),
      d_covSlv(d_env, d_im, d_model),
      d_icpSlv(d_env, d_im),
      d_iandSlv(env, d_im, d_model),
      d_pow2Slv(env, d_im, d_model)
{
  d_extTheory.addFunctionKind(kind::NONLINEAR_MULT);
  d_extTheory.addFunctionKind(kind::EXPONENTIAL);
  d_extTheory.addFunctionKind(kind::SINE);
  d_extTheory.addFunctionKind(kind::PI);
  d_extTheory.addFunctionKind(kind::IAND);
  d_extTheory.addFunctionKind(kind::POW2);
  d_true = NodeManager::currentNM()->mkConst(true);
}

NonlinearExtension::~NonlinearExtension() {}

void NonlinearExtension::preRegisterTerm(TNode n)
{
  // register terms with extended theory, to find extended terms that can be
  // eliminated by context-depedendent simplification.
  d_extTheory.registerTerm(n);
}

void NonlinearExtension::processSideEffect(const NlLemma& se)
{
  d_trSlv.processSideEffect(se);
}

void NonlinearExtension::computeRelevantAssertions(
    const std::vector<Node>& assertions, std::vector<Node>& keep)
{
  const Valuation& v = d_containing.getValuation();
  for (const Node& a : assertions)
  {
    if (v.isRelevant(a))
    {
      keep.emplace_back(a);
    }
  }
  Trace("nl-ext-rlv") << "...relevant assertions: " << keep.size() << "/"
                      << assertions.size() << std::endl;
}

void NonlinearExtension::getAssertions(std::vector<Node>& assertions)
{
  Trace("nl-ext-assert-debug") << "Getting assertions..." << std::endl;
  bool useRelevance = false;
  if (options().arith.nlRlvMode == options::NlRlvMode::INTERLEAVE)
  {
    useRelevance = (d_checkCounter % 2);
  }
  else if (options().arith.nlRlvMode == options::NlRlvMode::ALWAYS)
  {
    useRelevance = true;
  }
  Valuation v = d_containing.getValuation();

  BoundInference bounds(d_env);

  std::unordered_set<Node> init_assertions;

  for (Theory::assertions_iterator it = d_containing.facts_begin();
       it != d_containing.facts_end();
       ++it)
  {
    const Assertion& assertion = *it;
    Trace("nl-ext-assert-debug")
        << "Loaded " << assertion.d_assertion << " from theory" << std::endl;
    Node lit = assertion.d_assertion;
    if (useRelevance && !v.isRelevant(lit))
    {
      // not relevant, skip
      continue;
    }
    // if using the bound inference utility
    if (options().arith.nlRlvAssertBounds && bounds.add(lit, false))
    {
      continue;
    }
    init_assertions.insert(lit);
  }

  for (const auto& vb : bounds.get())
  {
    const Bounds& b = vb.second;
    if (!b.lower_bound.isNull())
    {
      init_assertions.insert(b.lower_bound);
    }
    if (!b.upper_bound.isNull())
    {
      init_assertions.insert(b.upper_bound);
    }
  }

  // Try to be "more deterministic" by adding assertions in the order they were
  // given
  for (auto it = d_containing.facts_begin(); it != d_containing.facts_end();
       ++it)
  {
    Node lit = (*it).d_assertion;
    auto iait = init_assertions.find(lit);
    if (iait != init_assertions.end())
    {
      Trace("nl-ext-assert-debug") << "Adding " << lit << std::endl;
      assertions.push_back(lit);
      init_assertions.erase(iait);
    }
  }
  // Now add left over assertions that have been newly created within this
  // function by the code above.
  for (const Node& a : init_assertions)
  {
    Trace("nl-ext-assert-debug") << "Adding " << a << std::endl;
    assertions.push_back(a);
  }
  Trace("nl-ext") << "...keep " << assertions.size() << " / "
                  << d_containing.numAssertions() << " assertions."
                  << std::endl;
}

std::vector<Node> NonlinearExtension::getUnsatisfiedAssertions(
    const std::vector<Node>& assertions)
{
  std::vector<Node> false_asserts;
  for (const auto& lit : assertions)
  {
    Node litv = d_model.computeConcreteModelValue(lit);
    Trace("nl-ext-mv-assert") << "M[[ " << lit << " ]] -> " << litv;
    if (litv != d_true)
    {
      Trace("nl-ext-mv-assert") << " [model-false]";
      false_asserts.push_back(lit);
    }
    Trace("nl-ext-mv-assert") << std::endl;
  }
  return false_asserts;
}

bool NonlinearExtension::checkModel(const std::vector<Node>& assertions)
{
  Trace("nl-ext-cm") << "--- check-model ---" << std::endl;

  // get the presubstitution
  Trace("nl-ext-cm-debug") << "  apply pre-substitution..." << std::endl;
  // Notice that we do not consider relevance here, since assertions were
  // already filtered based on relevance. It is incorrect to filter based on
  // relevance here, since we may have discarded literals that are relevant
  // that are entailed based on the techniques in getAssertions.
  std::vector<Node> passertions = assertions;
  if (options().arith.nlExt == options::NlExtMode::FULL)
  {
    // preprocess the assertions with the trancendental solver
    if (!d_trSlv.preprocessAssertionsCheckModel(passertions))
    {
      return false;
    }
  }
  if (options().arith.nlCov)
  {
    d_covSlv.constructModelIfAvailable(passertions);
  }

  Trace("nl-ext-cm") << "-----" << std::endl;
  unsigned tdegree = d_trSlv.getTaylorDegree();
  std::vector<NlLemma> lemmas;
  bool ret = d_model.checkModel(passertions, tdegree, lemmas);
  for (const auto& al: lemmas)
  {
    d_im.addPendingLemma(al);
  }
  return ret;
}

void NonlinearExtension::checkFullEffort(std::map<Node, Node>& arithModel,
                                         const std::set<Node>& termSet)
{
  Trace("nl-ext") << "NonlinearExtension::checkFullEffort" << std::endl;

  d_hasNlTerms = true;
  if (options().arith.nlExtRewrites)
  {
    std::vector<Node> nred;
    if (!d_extTheory.doInferences(0, nred))
    {
      Trace("nl-ext") << "...sent no lemmas, # extf to reduce = " << nred.size()
                      << std::endl;
      if (nred.empty())
      {
        d_hasNlTerms = false;
      }
    }
    else
    {
      Trace("nl-ext") << "...sent lemmas." << std::endl;
    }
  }

  if (!hasNlTerms())
  {
    // no non-linear constraints, we are done
    return;
  }
  Trace("nl-ext") << "NonlinearExtension::interceptModel begin" << std::endl;
  d_model.reset(arithModel);
  // run a last call effort check
  Trace("nl-ext") << "interceptModel: do model-based refinement" << std::endl;
  Result::Status res = modelBasedRefinement(termSet);
  if (res == Result::SAT)
  {
    Trace("nl-ext") << "interceptModel: do model repair" << std::endl;
    // modify the model values
    d_model.getModelValueRepair(arithModel);
  }
  // must post-process model with transcendental solver, to ensure we don't
  // assign values for equivalence classes with transcendental function
  // applications
  d_trSlv.postProcessModel(arithModel, termSet);
}

Result::Status NonlinearExtension::modelBasedRefinement(
    const std::set<Node>& termSet)
{
  ++(d_stats.d_mbrRuns);
  d_checkCounter++;

  // get the assertions
  std::vector<Node> assertions;
  getAssertions(assertions);

  Trace("nl-ext-mv-assert")
      << "Getting model values... check for [model-false]" << std::endl;
  // get the assertions that are false in the model
  const std::vector<Node> false_asserts = getUnsatisfiedAssertions(assertions);
  Trace("nl-ext") << "# false asserts = " << false_asserts.size() << std::endl;

  // get the extended terms belonging to this theory
  std::vector<Node> xtsAll;
  d_extTheory.getTerms(xtsAll);
  // only consider those that are currently relevant based on the current
  // assertions, i.e. those contained in termSet
  std::vector<Node> xts;
  for (const Node& x : xtsAll)
  {
    if (termSet.find(x) != termSet.end())
    {
      xts.push_back(x);
    }
  }

  if (TraceIsOn("nl-ext-debug"))
  {
    Trace("nl-ext-debug") << "  processing NonlinearExtension::check : "
                          << std::endl;
    Trace("nl-ext-debug") << "     " << false_asserts.size()
                          << " false assertions" << std::endl;
    Trace("nl-ext-debug") << "     " << xts.size()
                          << " extended terms: " << std::endl;
    Trace("nl-ext-debug") << "       ";
    for (unsigned j = 0; j < xts.size(); j++)
    {
      Trace("nl-ext-debug") << xts[j] << " ";
    }
    Trace("nl-ext-debug") << std::endl;
  }

  // compute whether shared terms have correct values
  bool needsRecheck;
  do
  {
    d_model.resetCheck();
    needsRecheck = false;
    // complete_status:
    //   1 : we may answer SAT, -1 : we may not answer SAT, 0 : unknown
    int complete_status = 1;
    // We require a check either if an assertion is false or a shared term has
    // a wrong value
    if (!false_asserts.empty())
    {
      complete_status = 0;
      runStrategy(Theory::Effort::EFFORT_FULL, assertions, false_asserts, xts);
      if (d_im.hasSentLemma() || d_im.hasPendingLemma())
      {
        d_im.clearWaitingLemmas();
        return Result::UNSAT;
      }
    }
    Trace("nl-ext") << "Finished check with status : " << complete_status
                    << std::endl;

    // if we did not add a lemma during check and there is a chance for SAT
    if (complete_status == 0)
    {
      Trace("nl-ext")
          << "Check model based on bounds for irrational-valued functions..."
          << std::endl;
      // check the model based on simple solving of equalities and using
      // error bounds on the Taylor approximation of transcendental functions.
      if (checkModel(assertions))
      {
        complete_status = 1;
      }
      if (d_im.hasUsed())
      {
        d_im.clearWaitingLemmas();
        return Result::UNSAT;
      }
    }

    // if we have not concluded SAT
    if (complete_status != 1)
    {
      // flush the waiting lemmas
      if (d_im.hasWaitingLemma())
      {
        std::size_t count = d_im.numWaitingLemmas();
        d_im.flushWaitingLemmas();
        Trace("nl-ext") << "...added " << count << " waiting lemmas."
                        << std::endl;
        return Result::UNSAT;
      }

      // we are incomplete
      if (options().arith.nlExt == options::NlExtMode::FULL
          && options().arith.nlExtIncPrecision && d_model.usedApproximate())
      {
        d_trSlv.incrementTaylorDegree();
        needsRecheck = true;
        // increase precision for PI?
        // Difficult since Taylor series is very slow to converge
        Trace("nl-ext") << "...increment Taylor degree to "
                        << d_trSlv.getTaylorDegree() << std::endl;
      }
      else
      {
        Trace("nl-ext") << "...failed to send lemma in "
                           "NonLinearExtension, set incomplete"
                        << std::endl;
        d_containing.getOutputChannel().setModelUnsound(IncompleteId::ARITH_NL);
        return Result::UNKNOWN;
      }
    }
    d_im.clearWaitingLemmas();
  } while (needsRecheck);

  // did not add lemmas
  return Result::SAT;
}

void NonlinearExtension::runStrategy(Theory::Effort effort,
                                     const std::vector<Node>& assertions,
                                     const std::vector<Node>& false_asserts,
                                     const std::vector<Node>& xts)
{
  ++(d_stats.d_checkRuns);

  if (TraceIsOn("nl-strategy"))
  {
    for (const auto& a : assertions)
    {
      Trace("nl-strategy") << "Input assertion: " << a << std::endl;
    }
  }
  if (!d_strategy.isStrategyInit())
  {
    d_strategy.initializeStrategy(options());
  }

  auto steps = d_strategy.getStrategy();
  bool stop = false;
  while (!stop && steps.hasNext())
  {
    InferStep step = steps.next();
    Trace("nl-strategy") << "Step " << step << std::endl;
    switch (step)
    {
      case InferStep::BREAK: stop = d_im.hasPendingLemma(); break;
      case InferStep::FLUSH_WAITING_LEMMAS: d_im.flushWaitingLemmas(); break;
      case InferStep::COVERINGS_FULL: d_covSlv.checkFull(); break;
      case InferStep::COVERINGS_INIT: d_covSlv.initLastCall(assertions); break;
      case InferStep::NL_FACTORING:
        d_factoringSlv.check(assertions, false_asserts);
        break;
      case InferStep::IAND_INIT:
        d_iandSlv.initLastCall(assertions, false_asserts, xts);
        break;
      case InferStep::IAND_FULL: d_iandSlv.checkFullRefine(); break;
      case InferStep::IAND_INITIAL: d_iandSlv.checkInitialRefine(); break;
      case InferStep::POW2_INIT:
        d_pow2Slv.initLastCall(assertions, false_asserts, xts);
        break;
      case InferStep::POW2_FULL: d_pow2Slv.checkFullRefine(); break;
      case InferStep::POW2_INITIAL: d_pow2Slv.checkInitialRefine(); break;
      case InferStep::ICP:
        d_icpSlv.reset(assertions);
        d_icpSlv.check();
        break;
      case InferStep::NL_INIT:
        d_extState.init(xts);
        d_monomialBoundsSlv.init();
        d_monomialSlv.init(xts);
        break;
      case InferStep::NL_MONOMIAL_INFER_BOUNDS:
        d_monomialBoundsSlv.checkBounds(assertions, false_asserts);
        break;
      case InferStep::NL_MONOMIAL_MAGNITUDE0:
        d_monomialSlv.checkMagnitude(0);
        break;
      case InferStep::NL_MONOMIAL_MAGNITUDE1:
        d_monomialSlv.checkMagnitude(1);
        break;
      case InferStep::NL_MONOMIAL_MAGNITUDE2:
        d_monomialSlv.checkMagnitude(2);
        break;
      case InferStep::NL_MONOMIAL_SIGN: d_monomialSlv.checkSign(); break;
      case InferStep::NL_RESOLUTION_BOUNDS:
        d_monomialBoundsSlv.checkResBounds();
        break;
      case InferStep::NL_SPLIT_ZERO: d_splitZeroSlv.check(); break;
      case InferStep::NL_TANGENT_PLANES: d_tangentPlaneSlv.check(false); break;
      case InferStep::NL_TANGENT_PLANES_WAITING:
        d_tangentPlaneSlv.check(true);
        break;
      case InferStep::TRANS_INIT:
        d_trSlv.initLastCall(xts);
        break;
      case InferStep::TRANS_INITIAL:
        d_trSlv.checkTranscendentalInitialRefine();
        break;
      case InferStep::TRANS_MONOTONIC:
        d_trSlv.checkTranscendentalMonotonic();
        break;
      case InferStep::TRANS_TANGENT_PLANES:
        d_trSlv.checkTranscendentalTangentPlanes();
        break;
    }
  }

  Trace("nl-ext") << "finished strategy" << std::endl;
  Trace("nl-ext") << "  ...finished with " << d_im.numWaitingLemmas()
                  << " waiting lemmas." << std::endl;
  Trace("nl-ext") << "  ...finished with " << d_im.numPendingLemmas()
                  << " pending lemmas." << std::endl;
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
