/*********************                                                        */
/*! \file lazy_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Lazy proof utility
 **/

#include "expr/lazy_proof.h"

namespace CVC4 {

LazyCDProof::LazyCDProof(ProofNodeManager* pnm, context::Context* c)
: CDProof(pnm, c)
{
  
}

LazyCDProof::~LazyCDProof(){}

std::shared_ptr<ProofNode> LazyCDProof::getLazyProof(Node fact)
{
  // visited set false after preorder traversal, true after postorder traversal
  std::unordered_set<Node, NodeHashFunction> visited;
  std::unordered_set<Node, NodeHashFunction>::iterator it;
  std::vector<Node> visit;
  visit.push_back(fact);
  // ensure that the steps have been made
  
}

void LazyCDProof::addStep(Node expected, ProofGenerator * pg, bool forceOverwrite)
{
  std::map< Node, ProofGenerator * >::const_iterator it = d_gens.find(expected);
  if (it!=d_gens.end() && !forceOverwrite)
  {
    // don't overwrite something that is already there
    return;
  }
  // just store now
  d_gens[expected] = pg;
}

}  // namespace CVC4
