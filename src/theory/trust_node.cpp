/*********************                                                        */
/*! \file trust_node.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the trust node utility
 **/

#include "theory/trust_node.h"

#include "expr/proof_generator.h"

namespace CVC4 {
namespace theory {

const char* toString(TrustNodeKind tnk)
{
  switch (tnk)
  {
    case TrustNodeKind::CONFLICT: return "CONFLICT";
    case TrustNodeKind::LEMMA: return "LEMMA";
    case TrustNodeKind::PROP_EXP: return "PROP_EXP";
    case TrustNodeKind::REWRITE: return "REWRITE";
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
  Node ckey = getConflictProven(conf);
  // if a generator is provided, should confirm that it can prove it
  Assert(g == nullptr || g->hasProofFor(ckey));
  return TrustNode(TrustNodeKind::CONFLICT, ckey, g);
}

TrustNode TrustNode::mkTrustLemma(Node lem, ProofGenerator* g)
{
  Node lkey = getLemmaProven(lem);
  // if a generator is provided, should confirm that it can prove it
  Assert(g == nullptr || g->hasProofFor(lkey));
  return TrustNode(TrustNodeKind::LEMMA, lkey, g);
}

TrustNode TrustNode::mkTrustPropExp(TNode lit, Node exp, ProofGenerator* g)
{
  Node pekey = getPropExpProven(lit, exp);
  Assert(g == nullptr || g->hasProofFor(pekey));
  return TrustNode(TrustNodeKind::PROP_EXP, pekey, g);
}

TrustNode TrustNode::mkTrustRewrite(TNode n, Node nr, ProofGenerator* g)
{
  Node rkey = getRewriteProven(n, nr);
  Assert(g == nullptr || g->hasProofFor(rkey));
  return TrustNode(TrustNodeKind::REWRITE, rkey, g);
}

TrustNode TrustNode::null()
{
  return TrustNode(TrustNodeKind::INVALID, Node::null());
}

TrustNode::TrustNode(TrustNodeKind tnk, Node p, ProofGenerator* g)
    : d_tnk(tnk), d_proven(p), d_gen(g)
{
  // does not make sense to provide null node with generator
  Assert(!d_proven.isNull() || d_gen == nullptr);
}

TrustNodeKind TrustNode::getKind() const { return d_tnk; }

Node TrustNode::getNode() const
{
  switch (d_tnk)
  {
    // the node of lemma is the node itself
    case TrustNodeKind::LEMMA: return d_proven;
    // the node of the rewrite is the right hand side of EQUAL
    case TrustNodeKind::REWRITE: return d_proven[1];
    // the node of an explained propagation is the antecendant of an IMPLIES
    // the node of a conflict is underneath a NOT
    default: return d_proven[0];
  }
}

Node TrustNode::getProven() const { return d_proven; }
ProofGenerator* TrustNode::getGenerator() const { return d_gen; }

bool TrustNode::isNull() const { return d_proven.isNull(); }

Node TrustNode::getConflictProven(Node conf) { return conf.notNode(); }

Node TrustNode::getLemmaProven(Node lem) { return lem; }

Node TrustNode::getPropExpProven(TNode lit, Node exp)
{
  return NodeManager::currentNM()->mkNode(kind::IMPLIES, exp, lit);
}

Node TrustNode::getRewriteProven(TNode n, Node nr) { return n.eqNode(nr); }

std::ostream& operator<<(std::ostream& out, TrustNode n)
{
  out << "(trust " << n.getNode() << ")";
  return out;
}

}  // namespace theory
}  // namespace CVC4
