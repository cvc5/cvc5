/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class for mining interesting unsat queries from a stream of generated
 * expressions.
 */

#include "theory/quantifiers/query_generator_unsat.h"

#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "smt/env.h"
#include "util/random.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

QueryGeneratorUnsat::QueryGeneratorUnsat(Env& env) : QueryGenerator(env)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  // determine the options to use for the verification subsolvers we spawn
  // we start with the provided options
  d_subOptions.copyValues(d_env.getOptions());
  d_subOptions.writeQuantifiers().sygus = false;
  d_subOptions.writeSmt().produceProofs = true;
  d_subOptions.writeSmt().checkProofs = true;
  d_subOptions.writeSmt().produceModels = true;
  d_subOptions.writeSmt().checkModels = true;
}

bool QueryGeneratorUnsat::addTerm(Node n, std::vector<Node>& queries)
{
  Trace("sygus-qgen") << "Add term: " << n << std::endl;
  ensureBoolean(n);
  d_terms.push_back(n);

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
  NodeManager* nm = NodeManager::currentNM();
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
      Node qy = nm->mkAnd(activeTerms);
      Result r = checkCurrent(qy, currModel, queries);
      if (r.getStatus() == Result::UNSAT)
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

Result QueryGeneratorUnsat::checkCurrent(const Node& qy,
                                         std::vector<Node>& currModel,
                                         std::vector<Node>& queries)
{
  Trace("expr-miner-check") << "Check (qgu): " << qy << std::endl;
  std::unique_ptr<SolverEngine> queryChecker;
  SubsolverSetupInfo ssi(d_env, d_subOptions);
  initializeChecker(queryChecker, qy, ssi);
  Result r = queryChecker->checkSat();
  Trace("expr-miner-check") << "...result: " << r << std::endl;
  if (r.getStatus() == Result::UNSAT)
  {
    // if unsat, get the unsat core
    std::vector<Node> unsatCore;
    getUnsatCoreFromSubsolver(*queryChecker.get(), unsatCore);
    Assert(!unsatCore.empty());
    Trace("expr-miner-check") << "...unsat core: " << unsatCore << std::endl;
    d_cores.add(d_false, unsatCore);
  }
  else if (r.getStatus() == Result::SAT)
  {
    getModelFromSubsolver(*queryChecker.get(), d_skolems, currModel);
    Trace("expr-miner-check") << "...model: " << currModel << std::endl;
  }
  dumpQuery(qy, r, queries);
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
}  // namespace cvc5::internal
