/*********************                                                        */
/*! \file solution_filter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utilities for filtering solutions.
 **/

#include "theory/quantifiers/solution_filter.h"

#include <fstream>
#include "options/quantifiers_options.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "util/random.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

SolutionFilterStrength::SolutionFilterStrength() : d_isStrong(true) {}
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
    Assert(false);
    return true;
  }
  NodeManager* nm = NodeManager::currentNM();
  // Do i subsume the disjunction of all previous solutions? If so, we discard
  // this immediately
  if (!d_curr_sols.empty())
  {
    Node curr =
        d_curr_sols.size() == 1 ? d_curr_sols[0] : nm->mkNode(AND, d_curr_sols);
    Node imp = d_isStrong ? nm->mkNode(AND, n.negate(), curr)
                          : nm->mkNode(AND, n, curr.negate());
    Trace("sygus-sol-implied")
        << "  implies: check subsumed " << imp << "..." << std::endl;
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
  if (options::sygusFilterSolRevSubsume())
  {
    std::vector<Node> nsubsume;
    for (const Node& s : d_curr_sols)
    {
      Node imp = d_isStrong ? nm->mkNode(AND, s.negate(), n)
                            : nm->mkNode(AND, s, n.negate());
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
        Options& nodeManagerOptions = nm->getOptions();
        std::ostream* out = nodeManagerOptions.getOut();
        (*out) << "; (filtered " << s << ")" << std::endl;
      }
    }
    d_curr_sols.clear();
    d_curr_sols.insert(d_curr_sols.end(), nsubsume.begin(), nsubsume.end());
  }
  d_curr_sols.push_back(n);
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
