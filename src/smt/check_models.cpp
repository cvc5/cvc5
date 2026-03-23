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

#include "base/modal_exception.h"
#include "expr/non_closed_node_converter.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "options/strings_options.h"
#include "smt/env.h"
#include "smt/expand_definitions.h"
#include "smt/preprocessor.h"
#include "smt/set_defaults.h"
#include "smt/smt_solver.h"
#include "theory/rewriter.h"
#include "theory/smt_engine_subsolver.h"
#include "theory/type_enumerator.h"
#include "theory/theory_model.h"

using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace smt {

namespace {

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
      if (ttid!=tid)
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

bool collectFiniteTypeInfo(Env& env,
                           const TheoryModel* m,
                           TypeNode tn,
                           TypeEnumeratorProperties& tep,
                           std::unordered_set<TypeNode>& visited)
{
  if (visited.find(tn) != visited.end())
  {
    return true;
  }
  visited.insert(tn);
  if (tn.isUninterpretedSort())
  {
    tep.d_fixed_card[tn] = Integer(m->getDomainElements(tn).size());
    return true;
  }
  for (const TypeNode& ctn : tn)
  {
    if (!collectFiniteTypeInfo(env, m, ctn, tep, visited))
    {
      return false;
    }
  }
  return env.isFiniteType(tn);
}

Node evaluateFiniteFormula(Env& env,
                           const TheoryModel* m,
                           Node n,
                           TypeEnumeratorProperties& tep,
                           int64_t& budget);

Node evaluateFiniteQuantifier(Env& env,
                              const TheoryModel* m,
                              Node q,
                              TypeEnumeratorProperties& tep,
                              int64_t& budget,
                              size_t index,
                              const std::vector<Node>& vars,
                              const std::vector<TypeNode>& types,
                              std::vector<Node>& vals,
                              bool isForall)
{
  if (budget <= 0)
  {
    return Node::null();
  }
  if (index == vars.size())
  {
    Node inst = env.evaluate(q[1], vars, vals, true);
    return evaluateFiniteFormula(env, m, inst, tep, budget);
  }
  NodeManager* nm = env.getNodeManager();
  bool sawUnknown = false;
  TypeEnumerator te(types[index], &tep);
  for (; !te.isFinished(); ++te)
  {
    if (--budget < 0)
    {
      return Node::null();
    }
    vals.push_back(*te);
    Node rv = evaluateFiniteQuantifier(
        env, m, q, tep, budget, index + 1, vars, types, vals, isForall);
    vals.pop_back();
    if (rv.isNull())
    {
      sawUnknown = true;
      continue;
    }
    Assert(rv.isConst() && rv.getType().isBoolean());
    bool b = rv.getConst<bool>();
    if (isForall && !b)
    {
      return nm->mkConst(false);
    }
    if (!isForall && b)
    {
      return nm->mkConst(true);
    }
  }
  if (sawUnknown)
  {
    return Node::null();
  }
  return nm->mkConst(isForall);
}

Node evaluateFiniteFormula(Env& env,
                           const TheoryModel* m,
                           Node n,
                           TypeEnumeratorProperties& tep,
                           int64_t& budget)
{
  if (budget <= 0)
  {
    return Node::null();
  }
  n = env.getRewriter()->rewrite(n);
  if (n.getKind() == Kind::FORALL || n.getKind() == Kind::EXISTS)
  {
    std::unordered_set<TypeNode> visited;
    std::vector<Node> vars;
    std::vector<TypeNode> types;
    for (const Node& v : n[0])
    {
      if (!collectFiniteTypeInfo(env, m, v.getType(), tep, visited))
      {
        return Node::null();
      }
      vars.push_back(v);
      types.push_back(v.getType());
    }
    std::vector<Node> vals;
    return evaluateFiniteQuantifier(env,
                                    m,
                                    n,
                                    tep,
                                    budget,
                                    0,
                                    vars,
                                    types,
                                    vals,
                                    n.getKind() == Kind::FORALL);
  }
  Node v = m->getValue(n);
  return v.isConst() ? v : Node::null();
}

}  // namespace

CheckModels::CheckModels(Env& e) : EnvObj(e) {}

void CheckModels::checkModel(const TheoryModel* m,
                             const context::CDList<Node>& al,
                             bool hardFailure)
{
  // Throughout, we use verbose(1) to give diagnostic output.
  //
  // If this function is running, the user gave --check-model (or equivalent),
  // and if verbose(1) is on, the user gave --verbose (or equivalent).

  Node sepHeap, sepNeq;
  if (m->getHeapModel(sepHeap, sepNeq))
  {
    throw RecoverableModalException(
        "Cannot run check-model on a model with a separation logic heap.");
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

  Trace("check-model") << "checkModel: Check assertions..." << std::endl;
  std::unordered_map<Node, Node> cache;
  // the list of assertions that did not rewrite to true
  std::vector<Node> noCheckList;
  // Now go through all our user assertions checking if they're satisfied.
  for (const Node& assertion : al)
  {
    verbose(1) << "SolverEngine::checkModel(): checking assertion " << assertion
               << std::endl;

    // Evaluate the original assertion directly. Top-level substitutions are
    // applied by TheoryModel::getValue(), which is also where higher-order
    // symbol reconstruction now lives.
    Node n = assertion;
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

      n = d_env.getRewriter()->rewrite(n);
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
        if (logicInfo().isHigherOrder() && NonClosedNodeConverter::isClosed(d_env, n))
        {
          TypeEnumeratorProperties tep(options().quantifiers.finiteModelFind,
                                       options().strings.stringsAlphaCard);
          tep.d_fixed_usort_card = options().quantifiers.finiteModelFind;
          // Keep this bounded. The path is only intended as a last-mile
          // checker for small closed higher-order formulas under finite-model
          // finding.
          int64_t budget = 4096;
          Node fnval = evaluateFiniteFormula(d_env, m, n, tep, budget);
          if (!fnval.isNull())
          {
            nval = fnval;
            if (nval.isConst() && nval.getConst<bool>())
            {
              processed = true;
              break;
            }
          }
        }
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
          // Avoid the subsolver fallback for higher-order formulas. After
          // ho-elim model reconstruction, the fallback may spend substantial
          // time on closed higher-order formulas that we still cannot fully
          // evaluate here.
          if (options().smt.checkModelSubsolver
              && !logicInfo().isHigherOrder()
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
      // compute the theories involved, e.g. for the sake of issue tracking.
      // to ensure minimality, if this is a topmost AND, miniscope
      Node nmin = n;
      while (nmin.getKind() == Kind::AND)
      {
        for (const Node& nc : nmin)
        {
          if (m->getValue(nc) == nval)
          {
            nmin = nc;
            break;
          }
        }
      }
      // collect the theories of the assertion
      std::vector<TheoryId> theories;
      getTheoriesOf(d_env, nmin, theories);
      std::sort(theories.begin(), theories.end());
      ss << " {";
      for (TheoryId tid : theories)
      {
        if (tid != THEORY_BOOL)
        {
          ss << " " << tid;
        }
      }
      ss << " }";
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

}  // namespace smt
}  // namespace cvc5::internal
