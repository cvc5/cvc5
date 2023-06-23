/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for constructing and maintaining abstract values.
 */

#include "smt/check_models.h"

#include "base/modal_exception.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "smt/env.h"
#include "smt/expand_definitions.h"
#include "smt/preprocessor.h"
#include "smt/smt_solver.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"
#include "theory/trust_substitutions.h"

using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace smt {

CheckModels::CheckModels(Env& e) : EnvObj(e) {}

void CheckModels::checkModel(TheoryModel* m,
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
    verbose(1) << "SolverEngine::checkModel(): -- expands to " << n
               << std::endl;

    n = rewrite(n);
    verbose(1) << "SolverEngine::checkModel(): -- rewrites to " << n
               << std::endl;

    // We look up the value before simplifying. If n contains quantifiers,
    // this may increases the chance of finding its value before the node is
    // altered by simplification below.
    n = m->getValue(n);
    verbose(1) << "SolverEngine::checkModel(): -- get value : " << n
               << std::endl;

    if (n.isConst() && n.getConst<bool>())
    {
      // assertion is true, everything is fine
      continue;
    }

    // Otherwise, we did not succeed in showing the current assertion to be
    // true. This may either indicate that our model is wrong, or that we cannot
    // check it. The latter may be the case for several reasons.
    // One example is the occurrence of partial operators. Another example
    // are quantified formulas, which are not checkable, although we assign
    // them to true/false based on the satisfying assignment. However,
    // quantified formulas can be modified during preprocess, so they may not
    // correspond to those in the satisfying assignment. Hence we throw
    // warnings for assertions that do not simplify to either true or false.
    // Other theories such as non-linear arithmetic (in particular,
    // transcendental functions) also have the property of not being able to
    // be checked precisely here.
    // Note that warnings like these can be avoided for quantified formulas
    // by making preprocessing passes explicitly record how they
    // rewrite quantified formulas (see cvc4-wishues#43).
    if (!n.isConst())
    {
      // Not constant, print a less severe warning message here.
      warning()
          << "Warning : SolverEngine::checkModel(): cannot check simplified "
             "assertion : "
          << n << std::endl;
      noCheckList.push_back(n);
      continue;
    }
    // Assertions that simplify to false result in an InternalError or
    // Warning being thrown below (when hardFailure is false).
    verbose(1) << "SolverEngine::checkModel(): *** PROBLEM: EXPECTED `TRUE' ***"
               << std::endl;
    std::stringstream ss;
    ss << "SolverEngine::checkModel(): "
       << "ERRORS SATISFYING ASSERTIONS WITH MODEL:" << std::endl
       << "assertion:     " << assertion << std::endl
       << "simplifies to: " << n << std::endl
       << "expected `true'." << std::endl
       << "Run with `--check-models -v' for additional diagnostics.";
    if (hardFailure)
    {
      // internal error if hardFailure is true
      InternalError() << ss.str();
    }
    else
    {
      warning() << ss.str() << std::endl;
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
