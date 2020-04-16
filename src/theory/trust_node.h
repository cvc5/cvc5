/*********************                                                        */
/*! \file trust_node.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The trust node utility
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__TRUST_NODE_H
#define CVC4__THEORY__TRUST_NODE_H

#include "expr/node.h"
#include "expr/proof_node.h"

namespace CVC4 {
namespace theory {

class ProofGenerator;

/**
 * A trust node is a pair (F, G) where F is a formula and G is a proof
 * generator that can construct a proof for F if asked.
 * 
 * They are intended to be constructed by ProofGenerator objects and passed
 * to ProofOutputChannel by theory solvers.
 *
 * Notice that this is a convienence class for tracking what
 * lemmas are proven by which generators. The static functions for constructing
 * them check that the generator, if provided, is capable of proving the given
 * conflict or lemma, or an assertion failure occurs.
 */
class TrustNode
{
 public:
  /** Make a proven node for conflict */
  static TrustNode mkTrustConflict(Node conf, ProofGenerator* g = nullptr);
  /** Make a proven node for lemma */
  static TrustNode mkTrustLemma(Node lem, ProofGenerator* g = nullptr);
  /** The null proven node */
  static TrustNode null();
  ~TrustNode() {}
  /** get node */
  Node getNode() const;
  /** get generator */
  ProofGenerator* getGenerator() const;
  /** is null? */
  bool isNull() const;

 private:
  TrustNode(Node n, ProofGenerator* g = nullptr);
  /** The node */
  Node d_node;
  /** The generator */
  ProofGenerator* d_gen;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__TRUST_NODE_H */
