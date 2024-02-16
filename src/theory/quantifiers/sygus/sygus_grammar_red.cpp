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

#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

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
  std::map<Node, Node> ntSymMap;
  Node lam = g.getLambdaForRule(r, ntSymMap);

  return tset;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
