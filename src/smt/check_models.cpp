/*********************                                                        */
/*! \file check_models.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
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

  // Output the model
  Notice() << *m;

  NodeManager* nm = NodeManager::currentNM();
  Preprocessor* pp = d_smt.getPreprocessor();

  // We have a "fake context" for the substitution map (we don't need it
  // to be context-dependent)
  context::Context fakeContext;
  SubstitutionMap substitutions(&fakeContext,
                                /* substituteUnderQuantifiers = */ false);

  Trace("check-model") << "checkModel: Collect substitution..." << std::endl;
  for (size_t k = 0, ncmd = m->getNumCommands(); k < ncmd; ++k)
  {
    const DeclareFunctionNodeCommand* c =
        dynamic_cast<const DeclareFunctionNodeCommand*>(m->getCommand(k));
    Notice() << "SmtEngine::checkModel(): model command " << k << " : "
             << m->getCommand(k)->toString() << std::endl;
    if (c == nullptr)
    {
      // we don't care about DECLARE-DATATYPES, DECLARE-SORT, ...
      Notice() << "SmtEngine::checkModel(): skipping..." << std::endl;
      continue;
    }
    // We have a DECLARE-FUN:
    //
    // We'll first do some checks, then add to our substitution map
    // the mapping: function symbol |-> value

    Node func = c->getFunction();
    Node val = m->getValue(func);

    Notice() << "SmtEngine::checkModel(): adding substitution: " << func
             << " |-> " << val << std::endl;

    // (1) if the value is a lambda, ensure the lambda doesn't contain the
    // function symbol (since then the definition is recursive)
    if (val.getKind() == kind::LAMBDA)
    {
      // first apply the model substitutions we have so far
      Node n = substitutions.apply(val[1]);
      // now check if n contains func by doing a substitution
      // [func->func2] and checking equality of the Nodes.
      // (this just a way to check if func is in n.)
      SubstitutionMap subs(&fakeContext);
      Node func2 =
          nm->mkSkolem("", func.getType(), "", NodeManager::SKOLEM_NO_NOTIFY);
      subs.addSubstitution(func, func2);
      if (subs.apply(n) != n)
      {
        Notice() << "SmtEngine::checkModel(): *** PROBLEM: MODEL VALUE DEFINED "
                    "IN TERMS OF ITSELF ***"
                 << std::endl;
        std::stringstream ss;
        ss << "SmtEngine::checkModel(): ERRORS SATISFYING ASSERTIONS WITH "
              "MODEL:"
           << std::endl
           << "considering model value for " << func << std::endl
           << "body of lambda is:   " << val << std::endl;
        if (n != val[1])
        {
          ss << "body substitutes to: " << n << std::endl;
        }
        ss << "so " << func << " is defined in terms of itself." << std::endl
           << "Run with `--check-models -v' for additional diagnostics.";
        InternalError() << ss.str();
      }
    }

    // (2) check that the value is actually a value
    else if (!val.isConst())
    {
      // This is only a warning since it could have been assigned an
      // unevaluable term (e.g. an application of a transcendental function).
      // This parallels the behavior (warnings for non-constant expressions)
      // when checking whether assertions are satisfied below.
      Warning() << "Warning : SmtEngine::checkModel(): "
                << "model value for " << func << std::endl
                << "             is " << val << std::endl
                << "and that is not a constant (.isConst() == false)."
                << std::endl
                << "Run with `--check-models -v' for additional diagnostics."
                << std::endl;
    }

    // (3) check that it's the correct (sub)type
    // This was intended to be a more general check, but for now we can't do
    // that because e.g. "1" is an INT, which isn't a subrange type [1..10]
    // (etc.).
    else if (func.getType().isInteger() && !val.getType().isInteger())
    {
      Notice() << "SmtEngine::checkModel(): *** PROBLEM: MODEL VALUE NOT "
                  "CORRECT TYPE ***"
               << std::endl;
      InternalError()
          << "SmtEngine::checkModel(): ERRORS SATISFYING ASSERTIONS WITH "
             "MODEL:"
          << std::endl
          << "model value for " << func << std::endl
          << "             is " << val << std::endl
          << "value type is     " << val.getType() << std::endl
          << "should be of type " << func.getType() << std::endl
          << "Run with `--check-models -v' for additional diagnostics.";
    }

    // (4) checks complete, add the substitution
    Trace("check-model") << "Substitution: " << func << " :=> " << val
                         << std::endl;
    substitutions.addSubstitution(func, val);
  }

  Trace("check-model") << "checkModel: Check assertions..." << std::endl;
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  // Now go through all our user assertions checking if they're satisfied.
  for (const Node& assertion : *al)
  {
    Notice() << "SmtEngine::checkModel(): checking assertion " << assertion
             << std::endl;
    Node n = assertion;
    Notice() << "SmtEngine::checkModel(): -- rewritten form is " << Rewriter::rewrite(n) << std::endl;
    Node nr = Rewriter::rewrite(substitutions.apply(n));
    if (nr.isConst() && nr.getConst<bool>())
    {
      continue;
    }
    // Apply any define-funs from the problem.
    n = pp->expandDefinitions(n, cache);
    Notice() << "SmtEngine::checkModel(): -- expands to " << n << std::endl;

    // Apply our model value substitutions.
    n = substitutions.apply(n);
    Notice() << "SmtEngine::checkModel(): -- substitutes to " << n << std::endl;

    // We look up the value before simplifying. If n contains quantifiers,
    // this may increases the chance of finding its value before the node is
    // altered by simplification below.
    n = m->getValue(n);
    Notice() << "SmtEngine::checkModel(): -- get value : " << n << std::endl;

    // Simplify the result and replace the already-known ITEs (this is important
    // for ground ITEs under quantifiers).
    n = pp->simplify(n, true);
    Notice()
        << "SmtEngine::checkModel(): -- simplifies with ite replacement to  "
        << n << std::endl;

    // Apply our model value substitutions (again), as things may have been
    // simplified.
    n = substitutions.apply(n);
    Notice() << "SmtEngine::checkModel(): -- re-substitutes to " << n
             << std::endl;

    // As a last-ditch effort, ask model to simplify it.
    // Presently, this is only an issue for quantifiers, which can have a value
    // but don't show up in our substitution map above.
    n = m->getValue(n);
    Notice() << "SmtEngine::checkModel(): -- model-substitutes to " << n
             << std::endl;

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
  Trace("check-model") << "checkModel: Finish" << std::endl;
  Notice() << "SmtEngine::checkModel(): all assertions checked out OK !"
           << std::endl;
}

}  // namespace smt
}  // namespace CVC4
