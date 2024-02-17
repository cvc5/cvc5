/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of sygus_grammar_red.
 */

#include "theory/quantifiers/sygus/sygus_grammar_red.h"

#include "expr/attribute.h"
#include "expr/bound_var_manager.h"
#include "theory/rewriter.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/** An attribute for canonical variables used in this class */
struct GrammarRedFreeVarAttributeId
{
};
using GrammarRedFreeVarAttribute =
    expr::Attribute<GrammarRedFreeVarAttributeId, Node>;

void SygusGrammarReduce::minimize(SygusGrammar& g)
{
  const std::vector<Node>& nts = g.getNtSyms();
  for (const Node& v : nts)
  {
    minimize(g, v);
  }
}

void SygusGrammarReduce::minimize(SygusGrammar& g, const Node& v)
{
  std::vector<Node> rules = g.getRulesFor(v);
  Trace("sygus-grammar-norm") << "Rules " << v << " " << rules << std::endl;
  std::unordered_set<Node> allTerms;
  for (const Node& r : rules)
  {
    std::unordered_set<Node> tset = getGenericList(g, r);
    bool dup = false;
    // if any rule can simulate one of the variants of this rule, we are
    // redundant.
    for (const Node& t : tset)
    {
      if (allTerms.find(t) != allTerms.end())
      {
        Trace("sygus-grammar-red")
            << "... " << r << " is duplicate since we already have variant "
            << t << std::endl;
        g.removeRule(v, r);
        dup = true;
        break;
      }
    }
    // if not a duplicate, remember all the variants
    if (!dup)
    {
      allTerms.insert(tset.begin(), tset.end());
    }
  }
}

std::unordered_set<Node> SygusGrammarReduce::getGenericList(
    const SygusGrammar& g, const Node& r)
{
  Trace("sygus-grammar-red-debug") << "Compute variants of " << r << std::endl;
  std::unordered_set<Node> tset;
  std::map<Node, Node> mapToNtSym;
  Node lam = g.getLambdaForRule(r, mapToNtSym);
  if (lam.getKind() != Kind::LAMBDA)
  {
    Node lamr = extendedRewrite(lam);
    // if no arguments, there are no further variants
    tset.insert(lamr);
  }
  else
  {
    // otherwise, consider permutations of all variables introduced for the same
    // non-terminal group by non-terminal to set up variable swapping
    std::vector<std::pair<Node, size_t>> vlist;
    std::vector<Node> ntlist;
    std::map<Node, std::vector<Node>> ntvMap;
    BoundVarManager* bvm = NodeManager::currentNM()->getBoundVarManager();
    for (const Node& v : lam[0])
    {
      Assert(mapToNtSym.find(v) != mapToNtSym.end());
      Node nts = mapToNtSym[v];
      std::vector<Node>& vs = ntvMap[nts];
      if (vs.empty())
      {
        ntlist.push_back(nts);
      }
      vlist.emplace_back(nts, vs.size());
      Node cacheVal = BoundVarManager::getCacheValue(nts, vs.size());
      vs.push_back(
          bvm->mkBoundVar<GrammarRedFreeVarAttribute>(cacheVal, nts.getType()));
      // remember cache values to ensure determinism
      d_cacheValues.push_back(cacheVal);
    }
    // add all variants
    getGenericListRec(lam, tset, vlist, ntlist, ntvMap, 0, 0);
  }
  if (TraceIsOn("sygus-grammar-red"))
  {
    Trace("sygus-grammar-red") << "Variants of " << r << ":" << std::endl;
    for (const Node& t : tset)
    {
      Trace("sygus-grammar-red") << "  " << t << std::endl;
    }
  }
  return tset;
}

void SygusGrammarReduce::getGenericListRec(
    const Node& lam,
    std::unordered_set<Node>& tset,
    const std::vector<std::pair<Node, size_t>>& vlist,
    const std::vector<Node>& ntlist,
    std::map<Node, std::vector<Node>>& ntvMap,
    size_t ntindex,
    size_t vindex)
{
  // to avoid exponential behavior, stop if we have more than 10 variants
  // already
  if (tset.size() >= 10)
  {
    return;
  }
  if (ntindex == ntlist.size())
  {
    std::vector<Node> args;
    args.push_back(lam);
    for (const std::pair<Node, size_t>& v : vlist)
    {
      args.push_back(ntvMap[v.first][v.second]);
    }
    Node app = NodeManager::currentNM()->mkNode(Kind::APPLY_UF, args);
    // apply extended rewriting to maximize chances for duplication
    app = extendedRewrite(app);
    tset.insert(app);
    return;
  }
  Node nts = ntlist[ntindex];
  std::vector<Node>& ntvs = ntvMap[nts];
  if (vindex == ntvs.size())
  {
    // go to next non-terminal
    return getGenericListRec(lam, tset, vlist, ntlist, ntvMap, ntindex + 1, 0);
  }
  for (size_t i = vindex, nvars = ntvs.size(); i < nvars; i++)
  {
    // swap the variables
    std::swap(ntvs[i], ntvs[vindex]);
    // recurse
    getGenericListRec(lam, tset, vlist, ntlist, ntvMap, ntindex, vindex + 1);
    // revert
    std::swap(ntvs[i], ntvs[vindex]);
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
