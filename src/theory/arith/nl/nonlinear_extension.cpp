/*********************                                                        */
/*! \file nonlinear_extension.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Gereon Kremer, Tim King
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

#include "theory/arith/nl/nonlinear_extension.h"

#include "options/arith_options.h"
#include "options/theory_options.h"
#include "theory/arith/arith_state.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/bound_inference.h"
#include "theory/arith/theory_arith.h"
#include "theory/ext_theory.h"
#include "theory/theory_model.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

NonlinearExtension::NonlinearExtension(TheoryArith& containing,
                                       ArithState& state,
                                       eq::EqualityEngine* ee,
                                       ProofNodeManager* pnm)
    : d_containing(containing),
      d_im(containing.getInferenceManager()),
      d_needsLastCall(false),
      d_checkCounter(0),
      d_extTheoryCb(ee),
      d_extTheory(d_extTheoryCb,
                  containing.getSatContext(),
                  containing.getUserContext(),
                  containing.getOutputChannel()),
      d_model(containing.getSatContext()),
      d_trSlv(d_im, d_model, pnm, containing.getUserContext()),
      d_extState(d_im, d_model, pnm, containing.getUserContext()),
      d_factoringSlv(&d_extState),
      d_monomialBoundsSlv(&d_extState),
      d_monomialSlv(&d_extState),
      d_splitZeroSlv(&d_extState),
      d_tangentPlaneSlv(&d_extState),
      d_cadSlv(d_im, d_model),
      d_icpSlv(d_im),
      d_iandSlv(d_im, state, d_model),
      d_builtModel(containing.getSatContext(), false)
{
  d_extTheory.addFunctionKind(kind::NONLINEAR_MULT);
  d_extTheory.addFunctionKind(kind::EXPONENTIAL);
  d_extTheory.addFunctionKind(kind::SINE);
  d_extTheory.addFunctionKind(kind::PI);
  d_extTheory.addFunctionKind(kind::IAND);
  d_true = NodeManager::currentNM()->mkConst(true);
  d_zero = NodeManager::currentNM()->mkConst(Rational(0));
  d_one = NodeManager::currentNM()->mkConst(Rational(1));
  d_neg_one = NodeManager::currentNM()->mkConst(Rational(-1));

  ProofChecker* pc = pnm != nullptr ? pnm->getChecker() : nullptr;
  if (pc != nullptr)
  {
    d_proofChecker.registerTo(pc);
  }
}

NonlinearExtension::~NonlinearExtension() {}

void NonlinearExtension::preRegisterTerm(TNode n)
{
  // register terms with extended theory, to find extended terms that can be
  // eliminated by context-depedendent simplification.
  d_extTheory.registerTerm(n);
}

void NonlinearExtension::sendLemmas(const std::vector<NlLemma>& out)
{
  for (const NlLemma& nlem : out)
  {
    Trace("nl-ext-lemma") << "NonlinearExtension::Lemma : " << nlem.d_inference
                          << " : " << nlem.d_node << std::endl;
    d_im.addPendingArithLemma(nlem);
    d_stats.d_inferences << nlem.d_inference;
  }
}

void NonlinearExtension::processSideEffect(const NlLemma& se)
{
  d_trSlv.processSideEffect(se);
}

void NonlinearExtension::computeRelevantAssertions(
    const std::vector<Node>& assertions, std::vector<Node>& keep)
{
  Trace("nl-ext-rlv") << "Compute relevant assertions..." << std::endl;
  Valuation v = d_containing.getValuation();
  for (const Node& a : assertions)
  {
    if (v.isRelevant(a))
    {
      keep.push_back(a);
    }
  }
  Trace("nl-ext-rlv") << "...keep " << keep.size() << "/" << assertions.size()
                      << " assertions" << std::endl;
}

unsigned NonlinearExtension::filterLemma(NlLemma lem, std::vector<NlLemma>& out)
{
  Trace("nl-ext-lemma-debug")
      << "NonlinearExtension::Lemma pre-rewrite : " << lem.d_node << std::endl;
  lem.d_node = Rewriter::rewrite(lem.d_node);

  if (d_im.hasCachedLemma(lem.d_node, lem.d_property))
  {
    Trace("nl-ext-lemma-debug")
        << "NonlinearExtension::Lemma duplicate : " << lem.d_node << std::endl;
    return 0;
  }
  out.emplace_back(lem);
  return 1;
}

unsigned NonlinearExtension::filterLemmas(std::vector<NlLemma>& lemmas,
                                          std::vector<NlLemma>& out)
{
  if (options::nlExtEntailConflicts())
  {
    // check if any are entailed to be false
    for (const NlLemma& lem : lemmas)
    {
      Node ch_lemma = lem.d_node.negate();
      ch_lemma = Rewriter::rewrite(ch_lemma);
      Trace("nl-ext-et-debug")
          << "Check entailment of " << ch_lemma << "..." << std::endl;
      std::pair<bool, Node> et = d_containing.getValuation().entailmentCheck(
          options::TheoryOfMode::THEORY_OF_TYPE_BASED, ch_lemma);
      Trace("nl-ext-et-debug") << "entailment test result : " << et.first << " "
                               << et.second << std::endl;
      if (et.first)
      {
        Trace("nl-ext-et") << "*** Lemma entailed to be in conflict : "
                           << lem.d_node << std::endl;
        // return just this lemma
        if (filterLemma(lem, out) > 0)
        {
          lemmas.clear();
          return 1;
        }
      }
    }
  }

  unsigned sum = 0;
  for (const NlLemma& lem : lemmas)
  {
    sum += filterLemma(lem, out);
    d_containing.getOutputChannel().spendResource(
        ResourceManager::Resource::ArithNlLemmaStep);
  }
  lemmas.clear();
  return sum;
}

void NonlinearExtension::getAssertions(std::vector<Node>& assertions)
{
  Trace("nl-ext-assert-debug") << "Getting assertions..." << std::endl;
  bool useRelevance = false;
  if (options::nlRlvMode() == options::NlRlvMode::INTERLEAVE)
  {
    useRelevance = (d_checkCounter % 2);
  }
  else if (options::nlRlvMode() == options::NlRlvMode::ALWAYS)
  {
    useRelevance = true;
  }
  Valuation v = d_containing.getValuation();

  BoundInference bounds;

  std::unordered_set<Node, NodeHashFunction> init_assertions;

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
    if (bounds.add(lit, false))
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

std::vector<Node> NonlinearExtension::checkModelEval(
    const std::vector<Node>& assertions)
{
  std::vector<Node> false_asserts;
  for (size_t i = 0; i < assertions.size(); ++i)
  {
    Node lit = assertions[i];
    Node atom = lit.getKind() == NOT ? lit[0] : lit;
    Node litv = d_model.computeConcreteModelValue(lit);
    Trace("nl-ext-mv-assert") << "M[[ " << lit << " ]] -> " << litv;
    if (litv != d_true)
    {
      Trace("nl-ext-mv-assert") << " [model-false]" << std::endl;
      false_asserts.push_back(lit);
    }
    else
    {
      Trace("nl-ext-mv-assert") << std::endl;
    }
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
  if (options::nlExt())
  {
    // preprocess the assertions with the trancendental solver
    if (!d_trSlv.preprocessAssertionsCheckModel(passertions))
    {
      return false;
    }
  }
  if (options::nlCad())
  {
    d_cadSlv.constructModelIfAvailable(passertions);
  }

  Trace("nl-ext-cm") << "-----" << std::endl;
  unsigned tdegree = d_trSlv.getTaylorDegree();
  std::vector<NlLemma> lemmas;
  bool ret = d_model.checkModel(passertions, tdegree, lemmas);
  for (const auto& al: lemmas)
  {
    d_im.addPendingArithLemma(al);
  }
  return ret;
}

void NonlinearExtension::check(Theory::Effort e)
{
  Trace("nl-ext") << std::endl;
  Trace("nl-ext") << "NonlinearExtension::check, effort = " << e
                  << ", built model = " << d_builtModel.get() << std::endl;
  if (e == Theory::EFFORT_FULL)
  {
    d_extTheory.clearCache();
    d_needsLastCall = true;
    if (options::nlExtRewrites())
    {
      std::vector<Node> nred;
      if (!d_extTheory.doInferences(0, nred))
      {
        Trace("nl-ext") << "...sent no lemmas, # extf to reduce = "
                        << nred.size() << std::endl;
        if (nred.empty())
        {
          d_needsLastCall = false;
        }
      }
      else
      {
        Trace("nl-ext") << "...sent lemmas." << std::endl;
      }
    }
  }
  else
  {
    // If we computed lemmas during collectModelInfo, send them now.
    if (d_im.hasPendingLemma())
    {
      d_im.doPendingFacts();
      d_im.doPendingLemmas();
      d_im.doPendingPhaseRequirements();
      d_im.reset();
      return;
    }
    // Otherwise, we will answer SAT. The values that we approximated are
    // recorded as approximations here.
    TheoryModel* tm = d_containing.getValuation().getModel();
    for (std::pair<const Node, std::pair<Node, Node>>& a : d_approximations)
    {
      if (a.second.second.isNull())
      {
        tm->recordApproximation(a.first, a.second.first);
      }
      else
      {
        tm->recordApproximation(a.first, a.second.first, a.second.second);
      }
    }
    for (const auto& vw : d_witnesses)
    {
      tm->recordApproximation(vw.first, vw.second);
    }
  }
}

bool NonlinearExtension::modelBasedRefinement()
{
  ++(d_stats.d_mbrRuns);
  d_checkCounter++;

  // get the assertions
  std::vector<Node> assertions;
  getAssertions(assertions);

  Trace("nl-ext-mv-assert")
      << "Getting model values... check for [model-false]" << std::endl;
  // get the assertions that are false in the model
  const std::vector<Node> false_asserts = checkModelEval(assertions);
  Trace("nl-ext") << "# false asserts = " << false_asserts.size() << std::endl;

  // get the extended terms belonging to this theory
  std::vector<Node> xts;
  d_extTheory.getTerms(xts);

  if (Trace.isOn("nl-ext-debug"))
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
  unsigned num_shared_wrong_value = 0;
  std::vector<Node> shared_term_value_splits;
  // must ensure that shared terms are equal to their concrete value
  Trace("nl-ext-mv") << "Shared terms : " << std::endl;
  for (context::CDList<TNode>::const_iterator its =
           d_containing.shared_terms_begin();
       its != d_containing.shared_terms_end();
       ++its)
  {
    TNode shared_term = *its;
    // compute its value in the model, and its evaluation in the model
    Node stv0 = d_model.computeConcreteModelValue(shared_term);
    Node stv1 = d_model.computeAbstractModelValue(shared_term);
    d_model.printModelValue("nl-ext-mv", shared_term);
    if (stv0 != stv1)
    {
      num_shared_wrong_value++;
      Trace("nl-ext-mv") << "Bad shared term value : " << shared_term
                         << std::endl;
      if (shared_term != stv0)
      {
        // split on the value, this is non-terminating in general, TODO :
        // improve this
        Node eq = shared_term.eqNode(stv0);
        shared_term_value_splits.push_back(eq);
      }
      else
      {
        // this can happen for transcendental functions
        // the problem is that we cannot evaluate transcendental functions
        // (they don't have a rewriter that returns constants)
        // thus, the actual value in their model can be themselves, hence we
        // have no reference point to rule out the current model.  In this
        // case, we may set incomplete below.
      }
    }
  }
  Trace("nl-ext-debug") << "     " << num_shared_wrong_value
                        << " shared terms with wrong model value." << std::endl;
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
    if (!false_asserts.empty() || num_shared_wrong_value > 0)
    {
      complete_status = num_shared_wrong_value > 0 ? -1 : 0;
      runStrategy(Theory::Effort::EFFORT_FULL, assertions, false_asserts, xts);
      if (d_im.hasSentLemma() || d_im.hasPendingLemma())
      {
        d_im.clearWaitingLemmas();
        return true;
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
        return true;
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
        return true;
      }
      // resort to splitting on shared terms with their model value
      // if we did not add any lemmas
      if (num_shared_wrong_value > 0)
      {
        complete_status = -1;
        if (!shared_term_value_splits.empty())
        {
          for (const Node& eq : shared_term_value_splits)
          {
            Node req = Rewriter::rewrite(eq);
            Node literal = d_containing.getValuation().ensureLiteral(req);
            d_containing.getOutputChannel().requirePhase(literal, true);
            Trace("nl-ext-debug") << "Split on : " << literal << std::endl;
            Node split = literal.orNode(literal.negate());
            NlLemma nsplit(split, InferenceId::NL_SHARED_TERM_VALUE_SPLIT);
            d_im.addPendingArithLemma(nsplit, true);
          }
          if (d_im.hasWaitingLemma())
          {
            d_im.flushWaitingLemmas();
            Trace("nl-ext") << "...added " << d_im.numPendingLemmas()
                            << " shared term value split lemmas." << std::endl;
            return true;
          }
        }
        else
        {
          // this can happen if we are trying to do theory combination with
          // trancendental functions
          // since their model value cannot even be computed exactly
        }
      }

      // we are incomplete
      if (options::nlExt() && options::nlExtIncPrecision()
          && d_model.usedApproximate())
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
        d_containing.getOutputChannel().setIncomplete();
      }
    }
    else
    {
      // we have built a model
      d_builtModel = true;
    }
    d_im.clearWaitingLemmas();
  } while (needsRecheck);

  // did not add lemmas
  return false;
}

void NonlinearExtension::interceptModel(std::map<Node, Node>& arithModel)
{
  if (!needsCheckLastEffort())
  {
    // no non-linear constraints, we are done
    return;
  }
  Trace("nl-ext") << "NonlinearExtension::interceptModel begin" << std::endl;
  d_model.reset(d_containing.getValuation().getModel(), arithModel);
  // run a last call effort check
  if (!d_builtModel.get())
  {
    Trace("nl-ext") << "interceptModel: do model-based refinement" << std::endl;
    modelBasedRefinement();
  }
  if (d_builtModel.get())
  {
    Trace("nl-ext") << "interceptModel: do model repair" << std::endl;
    d_approximations.clear();
    d_witnesses.clear();
    // modify the model values
    d_model.getModelValueRepair(arithModel, d_approximations, d_witnesses);
  }
}

void NonlinearExtension::presolve()
{
  Trace("nl-ext") << "NonlinearExtension::presolve" << std::endl;
  d_builtModel = false;
}

void NonlinearExtension::runStrategy(Theory::Effort effort,
                                     const std::vector<Node>& assertions,
                                     const std::vector<Node>& false_asserts,
                                     const std::vector<Node>& xts)
{
  ++(d_stats.d_checkRuns);

  if (Trace.isOn("nl-strategy"))
  {
    for (const auto& a : assertions)
    {
      Trace("nl-strategy") << "Input assertion: " << a << std::endl;
    }
  }
  if (!d_strategy.isStrategyInit())
  {
    d_strategy.initializeStrategy();
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
      case InferStep::CAD_FULL: d_cadSlv.checkFull(); break;
      case InferStep::CAD_INIT: d_cadSlv.initLastCall(assertions); break;
      case InferStep::NL_FACTORING:
        d_factoringSlv.check(assertions, false_asserts);
        break;
      case InferStep::IAND_INIT:
        d_iandSlv.initLastCall(assertions, false_asserts, xts);
        break;
      case InferStep::IAND_FULL: d_iandSlv.checkFullRefine(); break;
      case InferStep::IAND_INITIAL: d_iandSlv.checkInitialRefine(); break;
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
}  // namespace CVC4
