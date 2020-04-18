/*********************                                                        */
/*! \file proof_skolem_cache.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of proof skolem cache
 **/

#include "expr/proof_skolem_cache.h"

using namespace CVC4::kind;

namespace CVC4 {

Node ProofSkolemCache::mkSkolem(Node v,
                                Node pred,
                                const std::string& prefix,
                                const std::string& comment,
                                int flags)
{
  Assert(v.getKind() == BOUND_VARIABLE);
  // make the witness term
  NodeManager* nm = NodeManager::currentNM();
  Node bvl = nm->mkNode(BOUND_VARIABLE_LIST, v);
  Node w = nm->mkNode(CHOICE, bvl, pred);
  // make the skolem
  Node k = nm->mkSkolem(prefix, v.getType(), comment, flags);
  d_witness[k] = w;
  d_witnessVar.push_back(k);
  d_witnessTerm.push_back(w);
  return k;
}

Node ProofSkolemCache::convertToWitnessForm(Node n) const
{
  if (d_witnessVar.empty())
  {
    return n;
  }
  return n.substitute(d_witnessVar.begin(),
                      d_witnessVar.end(),
                      d_witnessTerm.begin(),
                      d_witnessTerm.end());
}

}  // namespace CVC4
