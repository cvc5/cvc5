/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for constructing and maintaining abstract values.
 */

#include "smt/check_models.h"

#include "base/check.h"
#include "expr/node_algorithm.h"
#include "expr/non_closed_node_converter.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "smt/env.h"
#include "smt/expand_definitions.h"
#include "smt/preprocessor.h"
#include "smt/set_defaults.h"
#include "smt/smt_solver.h"
#include "theory/rewriter.h"
#include "theory/sep/sep_model_checker.h"
#include "theory/smt_engine_subsolver.h"
#include "theory/theory_model.h"
#include "theory/trust_substitutions.h"

using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace smt {

void getTheoriesOf(Env& env, const Node& n, std::vector<TheoryId>& theories)
{
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      // get the theories of the term and its type
      TheoryId tid = env.theoryOf(cur);
      if (std::find(theories.begin(), theories.end(), tid) == theories.end())
      {
        theories.push_back(tid);
      }
      TheoryId ttid = env.theoryOf(cur.getType());
      if (ttid != tid)
      {
        if (std::find(theories.begin(), theories.end(), ttid) == theories.end())
        {
          theories.push_back(ttid);
        }
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
}

/**
 * The " { THEORY_A THEORY_B }" annotation naming the theories involved in an
 * assertion the model does not satisfy, which is there for the sake of issue
 * tracking.
 *
 * To keep it minimal, if `n` is a topmost AND this first miniscopes to a
 * conjunct whose value in `m` is `val` as well. Pass a null `val` when there
 * is no per-conjunct value to minimise on, e.g. when the verdict came from a
 * subsolver rather than from evaluating `n` itself.
 */
std::string getTheoryAnnotation(Env& env, TheoryModel* m, Node n, Node val)
{
  // To ensure minimality, if this is a topmost AND, miniscope. The `changed`
  // guard is what makes this terminate: if no conjunct carries the value then
  // none of them accounts for the failure on its own, and without the guard
  // the loop would keep re-examining the same AND.
  bool changed = !val.isNull();
  while (changed && n.getKind() == Kind::AND)
  {
    changed = false;
    for (const Node& nc : n)
    {
      if (m->getValue(nc) == val)
      {
        n = nc;
        changed = true;
        break;
      }
    }
  }
  // collect the theories of the assertion
  std::vector<TheoryId> theories;
  getTheoriesOf(env, n, theories);
  std::sort(theories.begin(), theories.end());
  std::stringstream ss;
  ss << " {";
  for (TheoryId tid : theories)
  {
    if (tid != THEORY_BOOL)
    {
      ss << " " << tid;
    }
  }
  ss << " }";
  return ss.str();
}

CheckModels::CheckModels(Env& e) : EnvObj(e) {}

void CheckModels::checkModel(TheoryModel* m,
                             const context::CDList<Node>& al,
                             bool hardFailure)
{
  // Throughout, we use verbose(1) to give diagnostic output.
  //
  // If this function is running, the user gave --check-model (or equivalent),
  // and if verbose(1) is on, the user gave --verbose (or equivalent).

  // If the model has a separation logic heap, spatial assertions cannot be
  // evaluated by the generic model evaluator (getValue leaves them unchanged).
  // We instead evaluate such assertions directly against the concrete heap
  // model below; see the SEP_* handling in the assertion loop.
  Node sepHeap, sepNeq;
  bool hasHeapModel = m->getHeapModel(sepHeap, sepNeq);
  // Whether the heap model term is ground, which is what makes it describe
  // exactly one heap. Computed once here and passed to
  // checkSepAssertionWithSubsolver, which is the check that depends on it.
  bool heapIsGround = true;
  if (hasHeapModel)
  {
    // The heap model is supposed to be a concrete structure, and every check
    // below assumes it denotes exactly one heap. If it does not -- a points-to
    // whose data was left unspecified becomes a placeholder rather than a
    // value -- then nothing can be checked against it, and that is a defect in
    // the model rather than a limit of the checking. Say so once here, instead
    // of leaving it to be inferred from a bare "cannot check" against every
    // spatial assertion in the problem.
    std::unordered_set<Node> heapSyms;
    expr::getSymbols(sepHeap, heapSyms);
    expr::getSymbols(sepNeq, heapSyms);
    heapIsGround = heapSyms.empty();
    verbose(1) << "SolverEngine::checkModel(): separation logic heap model is "
               << sepHeap << ", with " << sepNeq << std::endl;
    if (!heapIsGround)
    {
      warning() << "Warning : SolverEngine::checkModel(): the separation logic "
                   "heap model is not concrete : "
                << sepHeap << std::endl
                << "It does not describe a single heap, so no separation logic "
                   "assertion can be checked against it."
                << std::endl;
    }
  }
  if (options().quantifiers.fmfFunWellDefined)
  {
    warning() << "Running check-model is not guaranteed to pass when fmf-fun "
                 "is enabled."
              << std::endl;
    // only throw warning
    hardFailure = false;
  }
  // expand definitions module and substitutions
  std::unordered_map<Node, Node> ecache;
  ExpandDefs expDef(d_env);

  theory::SubstitutionMap& sm = d_env.getTopLevelSubstitutions().get();
  Trace("check-model") << "checkModel: Check assertions..." << std::endl;
  std::unordered_map<Node, Node> cache;
  // the list of assertions that did not rewrite to true
  std::vector<Node> noCheckList;
  // Now go through all our user assertions checking if they're satisfied.
  for (const Node& assertion : al)
  {
    verbose(1) << "SolverEngine::checkModel(): checking assertion " << assertion
               << std::endl;

    // If the model has a heap and this assertion is a spatial formula, the
    // generic machinery below cannot decide it. getValue evaluates separation
    // logic atoms against the concrete heap model, so we rely on it here.
    if (hasHeapModel && sep::SepModelChecker::hasSpatialSubterm(assertion))
    {
      // Apply the same preprocessing the generic path below does, so that the
      // two decide the same formula. getValue applies the top-level
      // substitutions itself, but nothing else expands the definitions, which
      // is what makes operators that expand involving skolems during
      // preprocessing evaluate accurately rather than raising a spurious
      // warning. Definition expansion does not touch spatial operators, so the
      // result is still the spatial assertion we came here for.
      Node sn = expDef.expandDefinitions(sm.apply(assertion), cache);
      verbose(1) << "SolverEngine::checkModel(): -- expands to " << sn
                 << std::endl;
      Node sval = m->getValue(sn);
      verbose(1) << "SolverEngine::checkModel(): -- evaluates against the heap "
                    "model to "
                 << sval << std::endl;
      // Track whether the refuting verdict came from the subsolver cross-check
      // rather than direct evaluation. A subsolver refutation is a
      // cvc5-versus-cvc5 disagreement (the main solve claimed SAT with this
      // heap, but pinning the heap and re-checking is UNSAT), which is a
      // genuine separation logic soundness bug rather than a limitation of the
      // direct spatial-atom evaluator.
      bool viaSubsolver = false;
      if (!sval.isConst())
      {
        // getValue could not reduce the assertion to a Boolean. This happens
        // for assertions involving the separation magic wand, whose semantics
        // quantify over all extension heaps. As a secondary check, pin the heap
        // to the concrete model heap and re-check satisfiability with a
        // subsolver.
        sval = checkSepAssertionWithSubsolver(
            m, sepHeap, sepNeq, heapIsGround, sn);
        viaSubsolver = true;
        verbose(1) << "SolverEngine::checkModel(): -- subsolver with the heap "
                      "pinned says "
                   << (sval.isNull() ? "unknown" : sval.toString())
                   << std::endl;
      }
      if (sval.isNull() || !sval.isConst())
      {
        // Still could not determine whether the model satisfies the assertion.
        warning() << "Warning : SolverEngine::checkModel(): cannot check "
                     "separation logic assertion : "
                  << assertion << std::endl;
        noCheckList.push_back(sn);
        continue;
      }
      if (sval.getConst<bool>())
      {
        // assertion holds in the heap model, everything is fine
        continue;
      }
      // The heap model does not satisfy the assertion.
      verbose(1)
          << "SolverEngine::checkModel(): *** PROBLEM: EXPECTED `TRUE' ***"
          << std::endl;
      std::stringstream ss;
      ss << "SolverEngine::checkModel(): "
         << "ERRORS SATISFYING ASSERTIONS WITH MODEL";
      std::stringstream ssdet;
      ssdet << ":" << std::endl << "assertion:     " << assertion << std::endl;
      if (viaSubsolver)
      {
        ssdet << "separation logic assertion refuted by subsolver with the "
                 "model heap pinned."
              << std::endl;
      }
      else
      {
        ssdet << "does not hold in the separation logic heap model."
              << std::endl;
      }
      ssdet << "Run with `--check-models -v' for additional diagnostics.";
      if (hardFailure)
      {
        // Only direct evaluation gives a value per conjunct to minimise on: a
        // subsolver refutation is a statement about the assertion as a whole,
        // its conjuncts being the wands direct evaluation could not decide.
        ss << getTheoryAnnotation(
            d_env, m, sn, viaSubsolver ? Node::null() : sval);
        InternalError() << ss.str() << ssdet.str();
      }
      else
      {
        warning() << ss.str() << ssdet.str() << std::endl;
      }
      continue;
    }

    // Apply any define-funs from the problem. We do not expand theory symbols
    // like integer division here. Hence, the code below is not able to properly
    // evaluate e.g. divide-by-zero. This is intentional since the evaluation
    // is not trustworthy, since the UF introduced by expanding definitions may
    // not be properly constrained.
    Node n = sm.apply(assertion);
    verbose(1) << "SolverEngine::checkModel(): -- substitutes to " << n
               << std::endl;

    // Expand definitions, which is required for being accurate for operators
    // that expand involving skolems during preprocessing. Not doing this will
    // increase the spurious warnings raised by this class.
    n = expDef.expandDefinitions(n, cache);
    bool checkAgain = false;
    bool processed = false;
    Node nval;
    do
    {
      checkAgain = false;
      verbose(1) << "SolverEngine::checkModel(): -- expands to " << n
                 << std::endl;

      n = rewrite(n);
      verbose(1) << "SolverEngine::checkModel(): -- rewrites to " << n
                 << std::endl;

      nval = m->getValue(n);
      verbose(1) << "SolverEngine::checkModel(): -- get value : " << n
                 << std::endl;

      if (nval.isConst() && nval.getConst<bool>())
      {
        // assertion is true, everything is fine
        processed = true;
        break;
      }

      // Otherwise, we did not succeed in showing the current assertion to be
      // true. This may either indicate that our model is wrong, or that we
      // cannot check it. The latter may be the case for several reasons. One
      // example is the occurrence of partial operators. Another example are
      // quantified formulas, which are not checkable, although we assign them
      // to true/false based on the satisfying assignment. However, quantified
      // formulas can be modified during preprocess, so they may not correspond
      // to those in the satisfying assignment. Hence we throw warnings for
      // assertions that do not simplify to either true or false. Other theories
      // such as non-linear arithmetic (in particular, transcendental functions)
      // also have the property of not being able to be checked precisely here.
      // Note that warnings like these can be avoided for quantified formulas
      // by making preprocessing passes explicitly record how they
      // rewrite quantified formulas (see cvc4-wishues#43).
      if (!nval.isConst())
      {
        n = expDef.expandDefinitions(nval, cache);
        if (n != nval)
        {
          // It could be that we can expand again after simplifying. This is
          // the case e.g. if a quantified formula with division is simplified
          // to a quantifier-free formula.
          checkAgain = true;
        }
        else
        {
          // Note that we must be a "closed" term, i.e. one that can be
          // given in an assertion.
          if (options().smt.checkModelSubsolver
              && NonClosedNodeConverter::isClosed(d_env, nval))
          {
            Trace("check-model-subsolver") << "Query is " << nval << std::endl;
            // satisfiability call
            Options subOptions;
            subOptions.copyValues(options());
            smt::SetDefaults::disableChecking(subOptions);
            // initialize the subsolver
            SubsolverSetupInfo ssi(d_env, subOptions);
            std::unique_ptr<SolverEngine> checkModelChecker;
            initializeSubsolver(nodeManager(), checkModelChecker, ssi);
            checkModelChecker->assertFormula(nval);
            Result r = checkModelChecker->checkSat();
            Trace("check-model-subsolver") << "..result is " << r << std::endl;
            if (r == Result::SAT)
            {
              processed = true;
              break;
            }
          }
          // Not constant, print a less severe warning message here.
          warning() << "Warning : SolverEngine::checkModel(): cannot check "
                       "simplified "
                       "assertion : "
                    << nval << std::endl;
          noCheckList.push_back(nval);
          processed = true;
          break;
        }
      }
    } while (checkAgain);
    // If processed in the loop above, we go to the next term
    if (processed)
    {
      continue;
    }
    // Assertions that simplify to false result in an InternalError or
    // Warning being thrown below (when hardFailure is false).
    verbose(1) << "SolverEngine::checkModel(): *** PROBLEM: EXPECTED `TRUE' ***"
               << std::endl;
    std::stringstream ss;
    ss << "SolverEngine::checkModel(): "
       << "ERRORS SATISFYING ASSERTIONS WITH MODEL";
    std::stringstream ssdet;
    ssdet << ":" << std::endl
          << "assertion:     " << assertion << std::endl
          << "simplifies to: " << nval << std::endl
          << "expected `true'." << std::endl
          << "Run with `--check-models -v' for additional diagnostics.";
    if (hardFailure)
    {
      ss << getTheoryAnnotation(d_env, m, n, nval);
      // internal error if hardFailure is true
      InternalError() << ss.str() << ssdet.str();
    }
    else
    {
      warning() << ss.str() << ssdet.str() << std::endl;
    }
  }
  if (noCheckList.empty())
  {
    verbose(1) << "SolverEngine::checkModel(): all assertions checked out OK !"
               << std::endl;
    return;
  }
  // if the noCheckList is non-empty, we could expand definitions on this list
  // and check satisfiability

  Trace("check-model") << "checkModel: Finish" << std::endl;
}

Node CheckModels::checkSepAssertionWithSubsolver(TheoryModel* m,
                                                 TNode sepHeap,
                                                 TNode sepNeq,
                                                 bool heapIsGround,
                                                 TNode assertion)
{
  // Only attempt this when subsolver-based checking is enabled.
  if (!options().smt.checkModelSubsolver)
  {
    return Node::null();
  }
  // This whole technique rests on the heap term describing exactly one heap,
  // so that satisfiability of the query means satisfaction by *this* model.
  // That fails if the heap term is not ground: with
  // --default-function-value-mode=hole a points-to whose data is unspecified
  // gets a placeholder rather than a value, and the subsolver is then free to
  // pick the cell's contents, so a sat answer says nothing about this model.
  // (The same is not true of a placeholder elsewhere in the assertion, which
  // is genuinely unconstrained; letting the subsolver choose there reads as
  // "some completion of this model satisfies the assertion", which is what
  // the generic check-model subsolver does for the other theories too.)
  if (!heapIsGround)
  {
    Trace("check-model-subsolver")
        << "checkModel: heap model is not ground, cannot pin " << sepHeap
        << std::endl;
    return Node::null();
  }
  NodeManager* nm = assertion.getNodeManager();
  // Pin the free symbols of the assertion to their values in the model, so
  // that we check *this* model rather than searching for a different one.
  // TheoryModel::simplify substitutes and rewrites, which is what we want
  // here: the symbols include the operators of applications, whose model
  // values are lambdas, so the substitution can leave a lambda in operator
  // position, and the rewrite beta-reduces those and expands any constant
  // hiding a non-closed subterm, so that the closedness check below sees the
  // term we would actually assert.
  Node sassertion = m->simplify(assertion);
  // Pin the heap to the concrete heap model and separation nil to its value,
  // and conjoin the (symbol-substituted) assertion. The heap model term
  // describes exactly one heap, so this query is satisfiable if and only if
  // the model heap satisfies the assertion.
  Assert(!sepNeq.isNull());
  Node query = nm->mkAnd(std::vector<Node>{sepHeap, sepNeq, sassertion});
  Trace("check-model-subsolver") << "Query is " << query << std::endl;
  // The query must be a closed formula to be assertable.
  if (!NonClosedNodeConverter::isClosed(d_env, query))
  {
    Trace("check-model-subsolver")
        << "checkModel: query is not closed, cannot assert it" << std::endl;
    return Node::null();
  }
  // Use a subsolver with all checking disabled, to avoid recursively invoking
  // check-models on the subsolver's own model.
  Options subOptions;
  subOptions.copyValues(options());
  smt::SetDefaults::disableChecking(subOptions);
  SubsolverSetupInfo ssi(d_env, subOptions);
  Result r = checkWithSubsolver(query, ssi);
  Trace("check-model-subsolver") << "checkModel: subsolver result for "
                                 << assertion << " is " << r << std::endl;
  if (r.getStatus() == Result::SAT)
  {
    return nm->mkConst(true);
  }
  if (r.getStatus() == Result::UNSAT)
  {
    return nm->mkConst(false);
  }
  // unknown: could not determine
  return Node::null();
}

}  // namespace smt
}  // namespace cvc5::internal
