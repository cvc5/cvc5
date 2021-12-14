/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class for mining interesting unsat queries from a stream of generated
 * expressions.
 */

#include "theory/quantifiers/query_generator_unsat.h"

#include "options/smt_options.h"
#include "smt/env.h"
#include "util/random.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

QueryGeneratorUnsat::QueryGeneratorUnsat(Env& env)
    : ExprMiner(env), d_queryCount(0)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  // determine the options to use for the verification subsolvers we spawn
  // we start with the provided options
  d_subOptions.copyValues(d_env.getOriginalOptions());
  d_subOptions.smt.produceProofs = true;
  d_subOptions.smt.checkProofs = true;
  d_subOptions.smt.produceModels = true;
  d_subOptions.smt.checkModels = true;
}

void QueryGeneratorUnsat::initialize(const std::vector<Node>& vars,
                                     SygusSampler* ss)
{
  Assert(ss != nullptr);
  d_queryCount = 0;
  ExprMiner::initialize(vars, ss);
}

bool QueryGeneratorUnsat::addTerm(Node n, std::ostream& out)
{
  d_terms.push_back(n);
  Trace("sygus-qgen") << "Add term: " << n << std::endl;
  Assert(n.getType().isBoolean());

  // the loop below conjoins a random subset of predicates we have enumerated
  // so far C1 ^ ... ^ Cn such that no subset of C1 ... Cn is an unsat core
  // we have encountered so far, and each appended Ci is false on a model for
  // C1 ^ ... ^ C_{i-1}.
  std::vector<Node> currModel;
  std::unordered_set<size_t> processed;
  std::vector<Node> activeTerms;
  // always start with the new term
  processed.insert(d_terms.size() - 1);
  activeTerms.push_back(n);
  bool addSuccess = true;
  size_t checkCount = 0;
  while (checkCount < 10)
  {
    // if we just successfully added a term, do a satisfiability check
    if (addSuccess)
    {
      Assert(!activeTerms.empty());
      checkCount++;
      // check the current for satisfiability
      currModel.clear();
      // Shuffle active terms to maximize the different possible behaviors
      // in the subsolver. This is instead of making multiple queries with
      // the same assertion order for a subsequence.
      std::vector<Node> aTermCurr = activeTerms;
      std::shuffle(aTermCurr.begin(), aTermCurr.end(), Random::getRandom());
      Result r = checkCurrent(aTermCurr, out, currModel);
      if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
      {
        // exclude the last active term
        activeTerms.pop_back();
      }
    }
    if (processed.size() == d_terms.size())
    {
      break;
    }
    // activeTerms is satisfiable, add a new term
    size_t rindex = getNextRandomIndex(processed);
    Assert(rindex < d_terms.size());
    processed.insert(rindex);
    Node nextTerm = d_terms[rindex];
    // immediately check if is satisfied by the current model using the
    // evaluator, if so, don't conjoin the term.
    Node newTermEval;
    if (!currModel.empty())
    {
      Node nextTermSk = convertToSkolem(nextTerm);
      newTermEval = evaluate(nextTermSk, d_skolems, currModel);
    }
    if (newTermEval == d_true)
    {
      Trace("sygus-qgen-check-debug")
          << "...already satisfied " << convertToSkolem(nextTerm)
          << " for model " << d_skolems << " " << currModel << std::endl;
      addSuccess = false;
    }
    else
    {
      Trace("sygus-qgen-check-debug")
          << "...not satisfied " << convertToSkolem(nextTerm) << " for model "
          << d_skolems << " " << currModel << std::endl;
      activeTerms.push_back(nextTerm);
      addSuccess = !d_cores.hasSubset(activeTerms);
      if (!addSuccess)
      {
        Trace("sygus-qgen-check-debug")
            << "...already has unsat core " << nextTerm << std::endl;
        activeTerms.pop_back();
      }
    }
  }

  return true;
}

Result QueryGeneratorUnsat::checkCurrent(const std::vector<Node>& activeTerms,
                                         std::ostream& out,
                                         std::vector<Node>& currModel)
{
  NodeManager* nm = NodeManager::currentNM();
  Node qy = nm->mkAnd(activeTerms);
  Trace("sygus-qgen-check") << "Check: " << qy << std::endl;
  out << "(query " << qy << ")" << std::endl;
  std::unique_ptr<SolverEngine> queryChecker;
  initializeChecker(queryChecker, qy, d_subOptions, logicInfo());
  Result r = queryChecker->checkSat();
  Trace("sygus-qgen-check") << "..finished check got " << r << std::endl;
  if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
  {
    // if unsat, get the unsat core
    std::vector<Node> unsatCore;
    getUnsatCoreFromSubsolver(*queryChecker.get(), unsatCore);
    Assert(!unsatCore.empty());
    Trace("sygus-qgen-check") << "...unsat core: " << unsatCore << std::endl;
    d_cores.add(d_false, unsatCore);
  }
  else if (r.asSatisfiabilityResult().isSat() == Result::SAT)
  {
    getModelFromSubsolver(*queryChecker.get(), d_skolems, currModel);
    Trace("sygus-qgen-check") << "...model: " << currModel << std::endl;
  }
  return r;
}

size_t QueryGeneratorUnsat::getNextRandomIndex(
    const std::unordered_set<size_t>& processed) const
{
  Assert(!d_terms.empty());
  Assert(processed.size() < d_terms.size());
  size_t rindex = Random::getRandom().pick(0, d_terms.size() - 1);
  while (processed.find(rindex) != processed.end())
  {
    rindex++;
    if (rindex == d_terms.size())
    {
      rindex = 0;
    }
  }
  return rindex;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
