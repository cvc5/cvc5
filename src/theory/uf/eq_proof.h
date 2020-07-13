/*********************                                                        */
/*! \file eq_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A proof as produced by the equality engine.
 **
 **/

#include "cvc4_private.h"

#pragma once

#include <deque>
#include <memory>
#include <queue>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "theory/uf/equality_engine_types.h"

namespace CVC4 {

class CDProof;

namespace theory {
namespace eq {

/**
 * An equality proof.
 *
 * This represents the reasoning performed by the Equality Engine to derive
 * facts, represented in terms of the rules in MergeReasonType. Each proof step
 * is annotated with the rule id, the conclusion node and a vector of proofs of
 * the rule's premises.
 **/
class EqProof
{
 public:
  /** A custom pretty printer used for custom rules being those in
   * MergeReasonType. */
  class PrettyPrinter
  {
   public:
    virtual ~PrettyPrinter() {}
    virtual std::string printTag(unsigned tag) = 0;
  };

  EqProof() : d_id(MERGED_THROUGH_REFLEXIVITY) {}
  /** The proof rule for concluding d_node */
  unsigned d_id;
  /** The conclusion of this EqProof */
  Node d_node;
  /** The proofs of the premises for deriving d_node with d_id */
  std::vector<std::shared_ptr<EqProof>> d_children;
  /**
   * Debug print this proof on debug trace c with tabulation tb and pretty
   * printer prettyPrinter.
   */
  void debug_print(const char* c,
                   unsigned tb = 0,
                   PrettyPrinter* prettyPrinter = nullptr) const;
  /**
   * Debug print this proof on output stream os with tabulation tb and pretty
   * printer prettyPrinter.
   */
  void debug_print(std::ostream& os,
                   unsigned tb = 0,
                   PrettyPrinter* prettyPrinter = nullptr) const;

  /** Add to proof
   *
   * Converts EqProof into ProofNode via a series of steps to be stored in
   * CDProof* p.
   *
   * This method can be seen as a best-effort solution until the EqualityEngine
   * is updated to produce ProofNodes directly, if ever. Note that since the
   * original EqProof steps can be coarse-grained (e.g. without proper order,
   * implicit inferences related to disequelaties) and are phrased over curried
   * terms, the transformation requires significant, although cheap (mostly
   * linear on the DAG-size of EqProof), post-processing.
   *
   * An important invariant of the resulting ProofNode is that neither its
   * assumptions nor its conclusion are predicate equalities, i.e. of the form
   * (= t true/false), modulo symmetry. This is so that users of the converted
   * ProofNode don't need to do case analysis on whether assumptions/conclusion
   * are either t or (= t true/false).
   *
   * @param p a pointer to a CDProof to store the conversion of this EqProof
   * @return the node that is the conclusion of the proof as added to p.
   */
  Node addToProof(CDProof* p) const;

 private:
  /**
   * As above, but with a cache of previously processed nodes and their results
   * (for DAG traversal). The caching is in terms of the original conclusions of
   * EqProof.
   */
  Node addToProof(
      CDProof* p,
      std::unordered_map<Node, Node, NodeHashFunction>& visited,
      std::unordered_set<Node, NodeHashFunction>& assumptions) const;

  /** Removes all reflexivity steps, i.e. (= t t), from premises. */
  void cleanReflPremises(std::vector<Node>& premises) const;

  /**
   *
   */
  bool foldTransitivityChildren(
      Node conclusion,
      std::vector<Node>& premises,
      CDProof* p,
      std::unordered_set<Node, NodeHashFunction>& assumptions) const;

  /**
   *
   *
   * This method assumes that premises does not contain reflexivity premises.
   * This is without loss of generality since such premisis are spurious for a
   * transitivity step.
   */
  bool buildTransitivityChain(Node conclusion,
                              std::vector<Node>& premises) const;

  void reduceNestedCongruence(
      unsigned i,
      Node conclusion,
      std::vector<std::vector<Node>>& children,
      CDProof* p,
      std::unordered_map<Node, Node, NodeHashFunction>& visited,
      std::unordered_set<Node, NodeHashFunction>& assumptions,
      bool isNary) const;

}; /* class EqProof */

}  // Namespace eq
}  // Namespace theory
}  // Namespace CVC4
