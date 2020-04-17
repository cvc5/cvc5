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

const char* toString(TrustNodeKind tnk)
{
  switch (tnk)
  {
    case TrustNodeKind::CONFLICT: return "CONFLICT";
    case TrustNodeKind::LEMMA: return "LEMMA";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, TrustNodeKind tnk)
{
  out << toString(tnk);
  return out;
}

TrustNode TrustNode::mkTrustConflict(Node conf, ProofGenerator* g)
{
  // if a generator is provided, should confirm that it can prove it
  Assert(d_gen == nullptr || d_gen->canProveConflict(conf));
  return TrustNode(TrustNodeKind::CONFLICT, conf, g);
}

TrustNode TrustNode::mkTrustLemma(Node lem, ProofGenerator* g)
{
  // if a generator is provided, should confirm that it can prove it
  Assert(d_gen == nullptr || d_gen->canProveLemma(lem));
  return TrustNode(TrustNodeKind::LEMMA, lem, g);
}

TrustNode TrustNode::null()
{
  return TrustNode(TrustNodeKind::INVALID, Node::null());
}

TrustNode::TrustNode(TrustNodeKind tnk, Node n, ProofGenerator* g)
    : d_tnk(tnk), d_node(n), d_gen(g)
{
  // does not make sense to provide null node with generator
  Assert(d_node.isNull() || d_gen != nullptr);
}

TrustNodeKind TrustNode::getKind() const { return d_tnk; }

Node TrustNode::getNode() const { return d_node; }

ProofGenerator* TrustNode::getGenerator() const { return d_gen; }

std::ostream& operator<<(std::ostream& out, TrustNode n)
{
  out << "(trust " << n.getNode() << ")";
  return out;
}

}  // namespace theory
}  // namespace CVC4
