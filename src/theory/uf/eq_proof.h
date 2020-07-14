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
   * if premises contain one equality between false and an equality then maybe
   * it'll be necessary to fix the transitivity premises before reaching the
   * original conclusion. For example
   *
   *  (= t1 t2) (= t3 t2) (= (t1 t3) false)
   *  ------------------------------------- TRANS
   *             false = true
   *
   * must, before the processing below, become
   *
   *            (= t3 t2)
   *            --------- SYMM
   *  (= t1 t2) (= t2 t3)
   *  ------------------- TRANS
   *       (= t1 t3)             (= (t1 t3) false)
   *  --------------------------------------------- TRANS
   *             false = true
   *
   * If the conclusion is, modulo symmetry, (= (= t1 t2) false), then the
   * above construction may fail. Consider
   *
   *  (= t3 t4) (= t3 t2) (= (t1 t2) false)
   *  ------------------------------------- TRANS
   *             (= (= t4 t1) false)
   *
   *  whose premises other than (= (t1 t2) false) do not allow the derivation
   *  of (= (= t1 t2) (= t4 t1)). The original conclusion however can be
   *  derived with
   *                          (= t2 t3) (= t3 t4)
   *                          ------------------- TRANS
   *  (= (t1 t2) false)           (= t2 t4)
   *  ------------------------------------------- MACRO_SR_PRED_TRANSFORM
   *             (= (= t4 t1) false)
   *
   * where note that the conclusion is equal to the left premise with the
   * right premise as a substitution applied to it, modulo rewriting (which
   * accounts for the different order of the equality with false).
   *
   * If in either of the above cases then the conclusion is directly derived
   * in the call, so only in the other cases we try to build a transitivity
   * step below
   */
  bool foldTransitivityChildren(
      Node conclusion,
      std::vector<Node>& premises,
      CDProof* p,
      std::unordered_set<Node, NodeHashFunction>& assumptions) const;

  /** Builds a transitivity chain from equalities to derive a conclusion
   *
   * Given an equality (= t1 tn), and a list of equalities premises, attempts to
   * build a chain (= t1 t2) ... (= tn-1 tn) from premises. This is done in a
   * greedy manner by finding one "link" in the chain at a time, updating the
   * conclusion to be the next link and the premises by removing the used
   * premise, and searching recursively.
   *
   * Consider for example
   * - conclusion: (= t1 t4)
   * - premises:   (= t4 t2), (= t2 t3), (= t2 t1), (= t3 t4)
   *
   * It proceeds by searching for t1 in an equality in the premises, in order,
   * which is found in the equality (= t2 t1). Since t2 != t4, it attempts to
   * build a chain with
   * - conclusion (= t2 t4)
   * - premises (= t4 t2), (= t2 t3), (= t3 t4)
   *
   * In the first equality it finds t2 and also t4, which closes the chain, so
   * that premises is updated to (= t2 t4) and the method returns true. Since
   * the recursive call was successful, the original conclusion (= t1 t4) is
   * justified with (= t1 t2) plus the chain built in the recursive call,
   * i.e. (= t1 t2), (= t2 t4).
   *
   * Note that not all the premises were necessary to build a successful
   * chain. Moreover, note that building a successful chain can depend on the
   * order in which the equalities are chosen. When a recursive call fails to
   * close a chain, the chosen equality is dismissed and another is searched for
   * among the remaining ones.
   *
   * This method assumes that premises does not contain reflexivity premises.
   * This is without loss of generality since such premises are spurious for a
   * transitivity step.
   *
   * @param conclusion the conclusion of the transitivity chain of equalities
   * @param premises the list of equalities to build a chain with
   * @return whether premises successfully build a transitivity chain for the
   * conclusion
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
