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

void SygusRedundantCons::minimize(SygusGrammar& g)
{
  const std::vector<Node>& nts = g.getNtSyms();
  for (const Node& v : nts)
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
}

std::unordered_set<Node> SygusRedundantCons::getGenericList(
    const SygusGrammar& g, const Node& r)
{
  std::unordered_set<Node> tset;
  std::map<Node, Node> mapToNtSym;
  Node lam = g.getLambdaForRule(r, mapToNtSym);
  if (lam.getKind() != Kind::LAMBDA)
  {
    tset.insert(lam);
  }
  else
  {
    // group by non-terminal
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
    }
    getGenericListRec(lam, tset, vlist, ntlist, ntvMap, 0, 0, 0);
  }
  return tset;
}

void SygusRedundantCons::getGenericListRec(const Node& lam,
                        std::unordered_set<Node>& tset,
                        const std::vector<std::pair<Node, size_t>>& vlist,
                      const std::vector<Node>& ntlist,
                      std::map<Node, std::vector<Node>>& ntvMap,
                      size_t ntindex,
                        size_t vindex,
                        size_t count)
{
  if (ntindex==ntlist.size())
  {
    std::vector<Node> args;
    args.push_back(lam);
    for (const std::pair<Node, size_t>& v : vlist)
    {
      args.push_back(ntvMap[v.first][v.second]);
    }
    Node app = NodeManager::currentNM()->mkNode(Kind::APPLY_UF, args);
    app = extendedRewrite(app);
    tset.insert(app);
    return;
  }
  Node nts = ntlist[ntindex];
  std::vector<Node>& ntvs = ntvMap[nts];
  Assert (vindex<ntvs.size());
  // don't consider swaps beyond >=5
  size_t endIndex = vindex+1;
  while (count<5 && endIndex<ntvs.size())
  {
    endIndex++;
    count++;
  }
  for (size_t i=vindex; i<endIndex; i++)
  {
    // swap the variables
    std::swap(ntvs[i], ntvs[vindex]);
    // recurse
    getGenericListRec(lam, tset, vlist, ntlist, ntvMap, ntindex, vindex+1, count);
    // revert
    std::swap(ntvs[i], ntvs[vindex]);
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
