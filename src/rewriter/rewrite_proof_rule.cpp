/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Hans-Jörg Schurr, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * proof rewrite rule class
 */

#include "rewriter/rewrite_proof_rule.h"

#include <sstream>

#include "expr/nary_term_util.h"
#include "expr/node_algorithm.h"
#include "proof/proof_checker.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace rewriter {

RewriteProofRule::RewriteProofRule() : d_id(ProofRewriteRule::NONE) {}

void RewriteProofRule::init(ProofRewriteRule id,
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

ProofRewriteRule RewriteProofRule::getId() const { return d_id; }

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
  std::map<Node, Node>::const_iterator it = d_listVarCtx.find(v);
  if (it != d_listVarCtx.end())
  {
    return it->second.getKind();
  }
  return Kind::UNDEFINED_KIND;
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

Node RewriteProofRule::getConclusion(bool includeContext) const
{
  Node conc = d_conc;
  // if the rule has conclusion s, and term context (lambda x. t[x]), then the
  // conclusion is t[s], which we compute in the block below.
  if (includeContext && isFixedPoint())
  {
    Node context = d_context;
    Node rhs = context[1].substitute(TNode(context[0][0]), TNode(conc[1]));
    conc = conc[0].eqNode(rhs);
  }
  return conc;
}

Node RewriteProofRule::getConclusionFor(const std::vector<Node>& ss) const
{
  Assert(d_fvs.size() == ss.size());
  Node conc = getConclusion(true);
  return expr::narySubstitute(conc, d_fvs, ss);
}

Node RewriteProofRule::getConclusionFor(
    const std::vector<Node>& ss,
    std::vector<std::pair<Kind, std::vector<Node>>>& witnessTerms) const
{
  Assert(d_fvs.size() == ss.size());
  Node conc = getConclusion(true);
  std::unordered_map<TNode, Node> visited;
  Node ret = expr::narySubstitute(conc, d_fvs, ss, visited);
  // also compute for the condition
  for (const Node& c : d_cond)
  {
    expr::narySubstitute(c, d_fvs, ss, visited);
  }
  std::map<Node, Node>::const_iterator itl;
  for (size_t i = 0, nfvs = ss.size(); i < nfvs; i++)
  {
    TNode v = d_fvs[i];
    Kind wk = Kind::UNDEFINED_KIND;
    std::vector<Node> wargs;
    if (!expr::isListVar(v))
    {
      // if not a list variable, it is the given term
      wargs.push_back(ss[i]);
    }
    else
    {
      itl = d_listVarCtx.find(v);
      Assert(itl != d_listVarCtx.end());
      Node ctx = itl->second;
      if (ss[i].getNumChildren() == 0)
      {
        // to determine the type, we get the type of the substitution of the
        // list context of the variable.
        Node subsCtx = visited[ctx];
        Assert(!subsCtx.isNull()) << "Failed to get context for " << ctx << " in " << d_id;
        Node nt = expr::getNullTerminator(ctx.getKind(), subsCtx.getType());
        wargs.push_back(nt);
      }
      else
      {
        wk = ctx.getKind();
        wargs.insert(wargs.end(), ss[i].begin(), ss[i].end());
      }
    }
    witnessTerms.emplace_back(wk, wargs);
  }
  return ret;
}

bool RewriteProofRule::isFixedPoint() const
{
  return d_context != Node::null();
}
}  // namespace rewriter
}  // namespace cvc5::internal
