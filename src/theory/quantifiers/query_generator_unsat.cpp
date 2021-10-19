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
 * A class for mining interesting satisfiability queries from a stream
 * of generated expressions.
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
  d_false = NodeManager::currentNM()->mkConst(false);
  // determine the options to use for the verification subsolvers we spawn
  // we start with the provided options
  d_subOptions.copyValues(d_env.getOriginalOptions());
  d_subOptions.smt.produceProofs = true;
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

  std::unordered_set<size_t> processed;
  std::vector<Node> activeTerms;
  // always start with the new term
  processed.insert(d_terms.size() - 1);
  activeTerms.push_back(n);
  bool addSuccess = true;
  size_t checkCount = 0;
  while (checkCount<3)
  {
    Assert(!activeTerms.empty());
    // if we just successfully added a term, do a satisfiability check
    if (addSuccess)
    {
      checkCount++;
      // check the current for satisfiability
      Result r = checkCurrent(activeTerms, out);
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
    activeTerms.push_back(d_terms[rindex]);
    processed.insert(rindex);
    addSuccess = !d_cores.hasSubset(activeTerms);
    if (!addSuccess)
    {
      activeTerms.pop_back();
    }
  }

  return true;
}

Result QueryGeneratorUnsat::checkCurrent(const std::vector<Node>& activeTerms,
                                         std::ostream& out)
{
  NodeManager* nm = NodeManager::currentNM();
  Node qy = nm->mkAnd(activeTerms);
  Trace("sygus-qgen-check") << "Check: " << qy << std::endl;
  out << "(query " << qy << ")" << std::endl;
  std::unique_ptr<SolverEngine> queryChecker;
  initializeChecker(queryChecker, qy, d_subOptions, logicInfo());
  Result r;
  try
  {
    r = queryChecker->checkSat();
  }
  catch (const cvc5::Exception& e)
  {
    Trace("sygus-qgen-check") << "EXCEPTION: cvc5::Exception" << std::endl;
  }
  catch (const std::invalid_argument& e)
  {
    Trace("sygus-qgen-check")
        << "EXCEPTION: std::invalid_argument" << std::endl;
  }
  /*
  catch (const OptionException& e)
  {
    Trace("sygus-qgen-check") << "EXCEPTION: OptionException" << std::endl;
  }
  catch (const cvc5::RecoverableModalException& e)
  {
    Trace("sygus-qgen-check") << "EXCEPTION: RecoverableModalException" <<
  std::endl;
  }
  */
  if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
  {
    // if unsat, get the unsat core
    std::vector<Node> unsatCore;
    getUnsatCoreFromSubsolver(*queryChecker.get(), unsatCore);
    Assert(!unsatCore.empty());
    Trace("sygus-qgen-check") << "...unsat core: " << unsatCore << std::endl;
    d_cores.add(d_false, unsatCore);
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
