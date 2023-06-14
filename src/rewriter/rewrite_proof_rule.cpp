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
 * Rewrite proof rule class
 */

#include "rewriter/rewrite_proof_rule.h"

#include <sstream>

#include "expr/nary_term_util.h"
#include "expr/node_algorithm.h"
#include "proof/proof_checker.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace rewriter {

RewriteProofRule::RewriteProofRule()
    : d_id(DslPfRule::FAIL)
{
}

void RewriteProofRule::init(DslPfRule id,
                            const std::vector<Node>& userFvs,
                            const std::vector<Node>& fvs,
                            const std::vector<Node>& cond,
                            Node conc,
                            Node context)
{
  // not initialized yet
  Assert(d_cond.empty() && d_obGen.empty() && d_fvs.empty());
  d_id = id;
  d_userFvs = userFvs;
  for (const Node& c : cond)
  {
    if (!expr::getListVarContext(c, d_listVarCtx))
    {
      Unhandled()
          << "Ambiguous context for list variables in condition of rule " << id;
    }
    d_cond.push_back(c);
    d_obGen.push_back(c);
  }
  d_conc = conc;
  d_context = context;
  if (!expr::getListVarContext(conc, d_listVarCtx))
  {
    Unhandled() << "Ambiguous context for list variables in conclusion of rule "
                << id;
  }

  d_numFv = fvs.size();

  std::unordered_set<Node> fvsCond;
  for (const Node& c : d_cond)
  {
    expr::getFreeVariables(c, fvsCond);
  }
  for (const Node& v : fvs)
  {
    d_fvs.push_back(v);
    if (fvsCond.find(v) == fvsCond.end())
    {
      d_noOccVars.insert(v);
    }
  }
  // if fixed point, initialize match utility
  if (d_context != Node::null())
  {
    d_mt.addTerm(conc[0]);
  }
}

rewriter::DslPfRule RewriteProofRule::getId() const { return d_id; }

const char* RewriteProofRule::getName() const { return toString(d_id); }

const std::vector<Node>& RewriteProofRule::getUserVarList() const
{
  return d_userFvs;
}
const std::vector<Node>& RewriteProofRule::getVarList() const { return d_fvs; }
bool RewriteProofRule::isExplicitVar(Node v) const
{
  Assert(std::find(d_fvs.begin(), d_fvs.end(), v) != d_fvs.end());
  return d_noOccVars.find(v) != d_noOccVars.end();
}
Kind RewriteProofRule::getListContext(Node v) const
{
  std::map<Node, Kind>::const_iterator it = d_listVarCtx.find(v);
  if (it != d_listVarCtx.end())
  {
    return it->second;
  }
  return UNDEFINED_KIND;
}
bool RewriteProofRule::hasConditions() const { return !d_cond.empty(); }

const std::vector<Node>& RewriteProofRule::getConditions() const
{
  return d_cond;
}

bool RewriteProofRule::getObligations(const std::vector<Node>& vs,
                                      const std::vector<Node>& ss,
                                      std::vector<Node>& vcs) const
{
  // substitute into each condition
  for (const Node& c : d_obGen)
  {
    Node sc = expr::narySubstitute(c, vs, ss);
    vcs.push_back(sc);
  }
  return true;
}

void RewriteProofRule::getMatches(Node h, expr::NotifyMatch* ntm) const
{
  d_mt.getMatches(h, ntm);
}

Node RewriteProofRule::getConclusion() const { return d_conc; }

Node RewriteProofRule::getConclusionFor(const std::vector<Node>& ss) const
{
  Assert(d_fvs.size() == ss.size());
  Node conc = d_conc;
  // if the rule has conclusion s, and term context (lambda x. t[x]), then the
  // conclusion is t[s], which we compute in the block below.
  if (isFixedPoint())
  {
    Node context = d_context;
    Node rhs = context[1].substitute(TNode(context[0][0]), TNode(conc[1]));
    conc = conc[0].eqNode(rhs);
  }
  return expr::narySubstitute(conc, d_fvs, ss);
}
bool RewriteProofRule::isFixedPoint() const
{
  return d_context != Node::null();
}
}  // namespace rewriter
}  // namespace cvc5::internal
