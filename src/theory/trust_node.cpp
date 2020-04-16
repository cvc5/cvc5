/*********************                                                        */
/*! \file trust_node.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the trust node utility
 **/

#include "theory/trust_node.h"

namespace CVC4 {
namespace theory {

TrustNode TrustNode::mkTrustConflict(Node conf, ProofGenerator* g)
{
  // if a generator is provided, should confirm that it can prove it
  Assert(d_gen == nullptr || d_gen->canProveConflict(conf));
  return TrustNode(conf, g);
}

TrustNode TrustNode::mkTrustLemma(Node lem, ProofGenerator* g)
{
  // if a generator is provided, should confirm that it can prove it
  Assert(d_gen == nullptr || d_gen->canProveLemma(lem));
  return TrustNode(lem, g);
}

TrustNode TrustNode::null() { return TrustNode(Node::null()); }

TrustNode::TrustNode(Node n, ProofGenerator* g) : d_node(n), d_gen(g)
{
  // does not make sense to provide null node with generator
  Assert(d_node.isNull() || d_gen != nullptr);
}

Node TrustNode::getNode() const { return d_node; }

ProofGenerator* TrustNode::getGenerator() const { return d_gen; }

}  // namespace theory
}  // namespace CVC4
