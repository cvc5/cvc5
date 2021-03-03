/*********************                                                        */
/*! \file proof_bitblaster.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A bit-blaster wrapper around BBSimple for proof logging.
 **/
#include "theory/bv/bitblast/proof_bitblaster.h"

#include <unordered_set>

#include "theory/theory_model.h"

namespace CVC4 {
namespace theory {
namespace bv {

BBProof::BBProof(TheoryState* state) : d_bb(new BBSimple(state)) {}

void BBProof::bbAtom(TNode node)
{
  std::vector<TNode> visit;
  visit.push_back(node);
  std::unordered_set<TNode, TNodeHashFunction> visited;
  while (!visit.empty())
  {
    TNode n = visit.back();
    if (hasBBAtom(n) || hasBBTerm(n))
    {
      visit.pop_back();
      continue;
    }

    if (visited.find(n) == visited.end())
    {
      visited.insert(n);
      if (!Theory::isLeafOf(n, theory::THEORY_BV))
      {
        visit.insert(visit.end(), n.begin(), n.end());
      }
    }
    else
    {
      if (Theory::isLeafOf(n, theory::THEORY_BV) && !n.isConst())
      {
        // unused for now, will be needed for proof logging
        Bits bits;
        d_bb->makeVariable(n, bits);
      }
      else if (n.getType().isBitVector())
      {
        Bits bits;
        d_bb->bbTerm(n, bits);
      }
      else
      {
        d_bb->bbAtom(n);
      }
      visit.pop_back();
    }
  }
}

bool BBProof::hasBBAtom(TNode atom) const { return d_bb->hasBBAtom(atom); }

bool BBProof::hasBBTerm(TNode atom) const { return d_bb->hasBBTerm(atom); }

Node BBProof::getStoredBBAtom(TNode node)
{
  return d_bb->getStoredBBAtom(node);
}

bool BBProof::collectModelValues(TheoryModel* m,
                                 const std::set<Node>& relevantTerms)
{
  return d_bb->collectModelValues(m, relevantTerms);
}

}  // namespace bv
}  // namespace theory
}  // namespace CVC4
