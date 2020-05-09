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

namespace CVC4 {

class ProofGenerator;

namespace theory {

/** A kind for trust nodes */
enum class TrustNodeKind : uint32_t
{
  CONFLICT,
  LEMMA,
  PROP_EXP,
  INVALID
};
/**
 * Converts a proof rule to a string. Note: This function is also used in
 * `safe_print()`. Changing this function name or signature will result in
 * `safe_print()` printing "<unsupported>" instead of the proper strings for
 * the enum values.
 *
 * @param tnk The trust node kind
 * @return The name of the trust node kind
 */
const char* toString(TrustNodeKind tnk);

/**
 * Writes a trust node kind name to a stream.
 *
 * @param out The stream to write to
 * @param tnk The trust node kind to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, TrustNodeKind tnk);

/**
 * A trust node is a pair (F, G) where F is a formula and G is a proof
 * generator that can construct a proof for F if asked.
 *
 * More generally, a trust node is any node that can be used for a specific
 * purpose that requires justification, such as being passed to
 * OutputChannel::lemma. That justification is intended to be given by the
 * generator that is required to construct this object.
 *
 * They are intended to be constructed by ProofGenerator objects themselves (a
 * proof generator wraps itself in TrustNode it returns) and passed
 * to ProofOutputChannel by theory solvers.
 *
 * The static functions for constructing them check that the generator, if
 * provided, is capable of proving the given conflict or lemma, or an assertion
 * failure occurs. Otherwise an assertion error is given.
 */
class TrustNode
{
 public:
  TrustNode() : d_tnk(TrustNodeKind::INVALID), d_gen(nullptr) {}
  /** Make a proven node for conflict */
  static TrustNode mkTrustConflict(Node conf, ProofGenerator* g = nullptr);
  /** Make a proven node for lemma */
  static TrustNode mkTrustLemma(Node lem, ProofGenerator* g = nullptr);
  /** Make a proven node for explanation of propagated literal */
  static TrustNode mkTrustPropExp(TNode lit,
                                  Node exp,
                                  ProofGenerator* g = nullptr);
  /** The null proven node */
  static TrustNode null();
  ~TrustNode() {}
  /** get kind */
  TrustNodeKind getKind() const;
  /** get node */
  Node getNode() const;
  /** get generator */
  ProofGenerator* getGenerator() const;
  /** is null? */
  bool isNull() const;

  /** Get the node key for which conflict calls are cached */
  static Node getConflictKeyValue(Node conf);
  /** Get the node key for which lemma calls are cached */
  static Node getLemmaKeyValue(Node lem);
  /** Get the node key for which explanations for propagations are cached */
  static Node getPropExpKeyValue(TNode lit, Node exp);
  /** Get the node key for the exp => conc */
  static Node getKeyValue(TrustNodeKind tnk, Node exp, Node conc);

 private:
  TrustNode(TrustNodeKind tnk, Node n, ProofGenerator* g = nullptr);
  /** The kind */
  TrustNodeKind d_tnk;
  /** The node */
  Node d_node;
  /** The generator */
  ProofGenerator* d_gen;
};

/**
 * Writes a trust node to a stream.
 *
 * @param out The stream to write to
 * @param n The trust node to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, TrustNode n);

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__TRUST_NODE_H */
