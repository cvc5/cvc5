/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of quantifier relevance.
 */

#include "theory/quantifiers/quant_relevance.h"

using namespace std;
using namespace cvc5::internal::kind;
using namespace cvc5::context;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

QuantRelevance::QuantRelevance(Env& env) : QuantifiersUtil(env) {}

void QuantRelevance::registerQuantifier(Node f)
{
  // compute symbols in f
  std::vector<Node> syms;
  computeSymbols(f[1], syms);
  d_syms[f].insert(d_syms[f].begin(), syms.begin(), syms.end());
}

/** compute symbols */
void QuantRelevance::computeSymbols(Node n, std::vector<Node>& syms)
{
  if (n.getKind() == APPLY_UF)
  {
    Node op = n.getOperator();
    if (std::find(syms.begin(), syms.end(), op) == syms.end())
    {
      syms.push_back(op);
    }
  }
  if (n.getKind() != FORALL)
  {
    for (int i = 0; i < (int)n.getNumChildren(); i++)
    {
      computeSymbols(n[i], syms);
    }
  }
}

size_t QuantRelevance::getNumQuantifiersForSymbol(Node s) const
{
  std::map<Node, std::vector<Node> >::const_iterator it = d_syms_quants.find(s);
  if (it == d_syms_quants.end())
  {
    return 0;
  }
  return it->second.size();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
