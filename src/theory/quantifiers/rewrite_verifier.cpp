/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class for finding unsoundness in the rewriter
 */

#include "theory/quantifiers/rewrite_verifier.h"

#include "expr/node_algorithm.h"
#include "smt/env.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

RewriteVerifier::RewriteVerifier(Env& env) : ExprMiner(env) {}

bool RewriteVerifier::addTerm(Node n, std::vector<Node>& rewrites)
{
  Node nr = rewrite(n);
  if (!checkEquivalent(n, nr))
  {
    std::stringstream ss;
    checkEquivalent(n, nr, &ss);
    Warning() << ss.str();
    rewrites.push_back(n.eqNode(nr));
    return true;
  }
  return false;
}

bool RewriteVerifier::checkEquivalent(Node bv, Node bvr, std::ostream* out)
{
  if (bv == bvr)
  {
    return true;
  }
  if (d_sampler == nullptr)
  {
    Assert(false) << "Expected a sampler to test rewrites";
    return true;
  }
  // check if it has variables from d_vars, if not, we only test one point
  std::unordered_set<Node> syms;
  expr::getFreeVariables(bv, syms);
  bool hasVar = false;
  for (const Node& sym : syms)
  {
    if (std::find(d_vars.begin(), d_vars.end(), sym) != d_vars.end())
    {
      hasVar = true;
      break;
    }
  }
  size_t npoints = hasVar ? d_sampler->getNumSamplePoints() : 1;
  Trace("sygus-rr-verify") << "Testing rewrite rule " << bv << " ---> " << bvr
                           << " over " << npoints << " points for " << d_vars
                           << std::endl;

  // see if they evaluate to same thing on all sample points
  bool ptDisequal = false;
  bool ptDisequalConst = false;
  size_t pt_index = 0;
  Node bve, bvre;
  // if we don't have variables from sample, further points don't matter
  for (size_t i = 0; i < npoints; i++)
  {
    // do not use the rewriter in the calls to evaluate here
    const std::vector<Node>& pt = d_sampler->getSamplePoint(i);
    Assert(pt.size() == d_vars.size());
    bve = evaluate(bv, d_vars, pt, false);
    bvre = evaluate(bvr, d_vars, pt, false);
    if (bve != bvre)
    {
      ptDisequal = true;
      pt_index = i;
      if (bve.isConst() && bvre.isConst())
      {
        ptDisequalConst = true;
        break;
      }
    }
  }
  Trace("sygus-rr-verify") << "...finished" << std::endl;
  // bv and bvr should be equivalent under examples
  if (ptDisequal)
  {
    std::vector<Node> vars;
    d_sampler->getVariables(vars);
    const std::vector<Node>& pt = d_sampler->getSamplePoint(pt_index);
    Assert(vars.size() == pt.size());
    std::stringstream ptOut;
    for (size_t i = 0, size = pt.size(); i < size; i++)
    {
      ptOut << "  " << vars[i] << " -> " << pt[i] << std::endl;
    }
    if (!ptDisequalConst)
    {
      d_env.verbose(1)
          << "Warning: " << bv << " and " << bvr
          << " evaluate to different (non-constant) values on point:"
          << std::endl;
      d_env.verbose(1) << ptOut.str();
      return true;
    }
    // we have detected unsoundness in the rewriter
    // debugging information
    if (out)
    {
      (*out) << "find-synth: terms " << bv << " and " << bvr
             << " are not equivalent for :" << std::endl;
      (*out) << ptOut.str();
      Assert(bve != bvre);
      (*out) << "where they evaluate to " << bve << " and " << bvre
             << std::endl;
    }
    return false;
  }
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
