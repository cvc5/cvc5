/*********************                                                        */
/*! \file check_models.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utility for constructing and maintaining abstract values.
 **/

#include "smt/check_models.h"

#include "options/smt_options.h"
#include "smt/node_command.h"
#include "smt/preprocessor.h"
#include "theory/rewriter.h"
#include "theory/substitutions.h"
#include "theory/theory_engine.h"

using namespace CVC4::theory;

namespace CVC4 {
namespace smt {

CheckModels::CheckModels(SmtSolver& s) : d_smt(s) {}
CheckModels::~CheckModels() {}

void CheckModels::checkModel(Model* m,
                             context::CDList<Node>* al,
                             bool hardFailure)
{
  // Throughout, we use Notice() to give diagnostic output.
  //
  // If this function is running, the user gave --check-model (or equivalent),
  // and if Notice() is on, the user gave --verbose (or equivalent).

  // check-model is not guaranteed to succeed if approximate values were used.
  // Thus, we intentionally abort here.
  if (m->hasApproximations())
  {
    throw RecoverableModalException(
        "Cannot run check-model on a model with approximate values.");
  }

  // Check individual theory assertions
  if (options::debugCheckModels())
  {
    TheoryEngine* te = d_smt.getTheoryEngine();
    Assert(te != nullptr);
    te->checkTheoryAssertionsWithModel(hardFailure);
  }

  Preprocessor* pp = d_smt.getPreprocessor();

  Trace("check-model") << "checkModel: Check assertions..." << std::endl;
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  // the list of assertions that did not rewrite to true
  std::vector<Node> noCheckList;
  // Now go through all our user assertions checking if they're satisfied.
  for (const Node& assertion : *al)
  {
    Notice() << "SmtEngine::checkModel(): checking assertion " << assertion
             << std::endl;

    // Apply any define-funs from the problem. We do not expand theory symbols
    // like integer division here. Hence, the code below is not able to properly
    // evaluate e.g. divide-by-zero. This is intentional since the evaluation
    // is not trustworthy, since the UF introduced by expanding definitions may
    // not be properly constrained.
    Node n = pp->expandDefinitions(assertion, cache, true);
    Notice() << "SmtEngine::checkModel(): -- expands to " << n << std::endl;

    n = Rewriter::rewrite(n);
    Notice() << "SmtEngine::checkModel(): -- rewrites to " << n << std::endl;

    // We look up the value before simplifying. If n contains quantifiers,
    // this may increases the chance of finding its value before the node is
    // altered by simplification below.
    n = m->getValue(n);
    Notice() << "SmtEngine::checkModel(): -- get value : " << n << std::endl;

    if (n.isConst() && n.getConst<bool>())
    {
      // assertion is true, everything is fine
      continue;
    }

    // Otherwise, we did not succeed in showing the current assertion to be
    // true. This may either indicate that our model is wrong, or that we cannot
    // check it. The latter may be the case for several reasons.
    // For example, quantified formulas are not checkable, although we assign
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
      Warning() << "Warning : SmtEngine::checkModel(): cannot check simplified "
                   "assertion : "
                << n << std::endl;
      noCheckList.push_back(n);
      continue;
    }
    // Assertions that simplify to false result in an InternalError or
    // Warning being thrown below (when hardFailure is false).
    Notice() << "SmtEngine::checkModel(): *** PROBLEM: EXPECTED `TRUE' ***"
             << std::endl;
    std::stringstream ss;
    ss << "SmtEngine::checkModel(): "
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
      Warning() << ss.str() << std::endl;
    }
  }
  if (noCheckList.empty())
  {
    Notice() << "SmtEngine::checkModel(): all assertions checked out OK !"
             << std::endl;
    return;
  }
  // if the noCheckList is non-empty, we could expand definitions on this list
  // and check satisfiability

  Trace("check-model") << "checkModel: Finish" << std::endl;
}

}  // namespace smt
}  // namespace CVC4
