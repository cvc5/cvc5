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
   * Converts EqProof into ProofNodes via a series of steps to be stored in p.
   *
   * This method can be seen as a temporary solution until the EqualityEngine is
   * updated to produce ProofNodes directly, if ever.
   *
   * It returns the node that is the conclusion of the proof as added to p.
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

  /** Removes all reflexivity steps, i.e. premises (= t t), from premises
   *
   * Such premisis are spurious for a trastivity steps. The reordering of
   * premises in a transtivity step assumes no such steps are part of the
   * premises.
   */
  void cleanReflPremisesInTranstivity(std::vector<Node>& premises) const;

  bool foldTransitivityChildren(
      Node conclusion,
      std::vector<Node>& premises,
      CDProof* p,
      std::unordered_set<Node, NodeHashFunction>& assumptions) const;

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
