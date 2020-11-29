/*********************                                                        */
/*! \file quant_relevance.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of quantifier relevance
 **/

#include "theory/quantifiers/quant_relevance.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace quantifiers {

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

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
