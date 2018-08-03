/*********************                                                        */
/*! \file expr_miner.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of expr_miner
 **/

#include "theory/quantifiers/expr_miner.h"

#include "theory/quantifiers/term_util.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

Node ExprMiner::convertToSkolem(Node n)
{
  std::vector<Node> fvs;
  TermUtil::computeVarContains(n, fvs);
  if (fvs.empty())
  {
    return n;
  }
  std::vector<Node> sks;
  // map to skolems
  NodeManager* nm = NodeManager::currentNM();
  for (unsigned i = 0, size = fvs.size(); i < size; i++)
  {
    Node v = fvs[i];
    std::map<Node, Node>::iterator itf = d_fv_to_skolem.find(v);
    if (itf == d_fv_to_skolem.end())
    {
      Node sk = nm->mkSkolem("rrck", v.getType());
      d_fv_to_skolem[v] = sk;
      sks.push_back(sk);
    }
    else
    {
      sks.push_back(itf->second);
    }
  }
  return n.substitute(fvs.begin(), fvs.end(), sks.begin(), sks.end());
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
