/*********************                                                        */
/*! \file quant_relevance.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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
  // set initial relevance
  int minRelevance = -1;
  for (int i = 0; i < (int)syms.size(); i++)
  {
    d_syms_quants[syms[i]].push_back(f);
    int r = getRelevance(syms[i]);
    if (r != -1 && (minRelevance == -1 || r < minRelevance))
    {
      minRelevance = r;
    }
  }
  if (minRelevance != -1)
  {
    setRelevance(f, minRelevance + 1);
  }
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

/** set relevance */
void QuantRelevance::setRelevance(Node s, int r)
{
  if (d_computeRel)
  {
    int rOld = getRelevance(s);
    if (rOld == -1 || r < rOld)
    {
      d_relevance[s] = r;
      if (s.getKind() == FORALL)
      {
        for (int i = 0; i < (int)d_syms[s].size(); i++)
        {
          setRelevance(d_syms[s][i], r);
        }
      }
      else
      {
        for (int i = 0; i < (int)d_syms_quants[s].size(); i++)
        {
          setRelevance(d_syms_quants[s][i], r + 1);
        }
      }
    }
  }
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
