/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for filtering solutions.
 */

#include "theory/quantifiers/solution_filter.h"

#include <fstream>

#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "smt/env.h"
#include "smt/logic_exception.h"
#include "util/random.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace quantifiers {

SolutionFilterStrength::SolutionFilterStrength(Env& env)
    : ExprMiner(env), d_isStrong(true)
{
}
void SolutionFilterStrength::initialize(const std::vector<Node>& vars,
                                        SygusSampler* ss)
{
  ExprMiner::initialize(vars, ss);
}

void SolutionFilterStrength::setLogicallyStrong(bool isStrong)
{
  d_isStrong = isStrong;
}

bool SolutionFilterStrength::addTerm(Node n, std::ostream& out)
{
  if (!n.getType().isBoolean())
  {
    // currently, should not register non-Boolean terms here
    std::stringstream ss;
    ss << "SyGuS solution filtering requires the grammar to "
          "generate Boolean terms only";
    throw LogicException(ss.str());
    return true;
  }
  Node basen = d_isStrong ? n : n.negate();
  NodeManager* nm = NodeManager::currentNM();
  // Do i subsume the disjunction of all previous solutions? If so, we discard
  // this immediately
  Node curr;
  if (!d_curr_sols.empty())
  {
    curr = d_curr_sols.size() == 1
               ? d_curr_sols[0]
               : nm->mkNode(d_isStrong ? OR : AND, d_curr_sols);
    Node imp = nm->mkNode(AND, basen.negate(), curr);
    Trace("sygus-sol-implied")
        << "  implies: check subsumed (strong=" << d_isStrong << ") " << imp
        << "..." << std::endl;
    // check the satisfiability query
    Result r = doCheck(imp);
    Trace("sygus-sol-implied") << "  implies: ...got : " << r << std::endl;
    if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
    {
      // it is subsumed by the current, discard this
      return false;
    }
  }
  // check which solutions would have been filtered if the current had come
  // first
  if (options().quantifiers.sygusFilterSolRevSubsume)
  {
    std::vector<Node> nsubsume;
    for (const Node& s : d_curr_sols)
    {
      Node imp = nm->mkNode(AND, s.negate(), basen);
      Trace("sygus-sol-implied")
          << "  implies: check subsuming " << imp << "..." << std::endl;
      // check the satisfiability query
      Result r = doCheck(imp);
      Trace("sygus-sol-implied") << "  implies: ...got : " << r << std::endl;
      if (r.asSatisfiabilityResult().isSat() != Result::UNSAT)
      {
        nsubsume.push_back(s);
      }
      else
      {
        const Options& opts = d_env.getOptions();
        std::ostream* smtOut = opts.base.out;
        (*smtOut) << "; (filtered " << (d_isStrong ? s : s.negate()) << ")"
                  << std::endl;
      }
    }
    d_curr_sols.clear();
    d_curr_sols.insert(d_curr_sols.end(), nsubsume.begin(), nsubsume.end());
  }
  d_curr_sols.push_back(basen);
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
