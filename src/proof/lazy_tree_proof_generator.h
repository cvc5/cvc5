/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The lazy tree proof generator class.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__LAZY_TREE_PROOF_GENERATOR_H
#define CVC5__PROOF__LAZY_TREE_PROOF_GENERATOR_H

#include <iostream>

#include "expr/node.h"
#include "proof/proof_generator.h"
#include "proof/proof_node_manager.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace detail {
/**
 * A single node in the proof tree created by the LazyTreeProofGenerator.
 * A node directly represents a ProofNode that is eventually constructed from
 * it. The Nodes of the additional field d_premise are added to d_children as
 * new assumptions via ASSUME.
 * The object id can be used to store an arbitrary id to identify tree nodes
 * and map them back to some other type, for example during pruning.
 */
struct TreeProofNode
{
  /** Storage for some custom object identifier, used for pruning */
  size_t d_objectId;
  /** The proof rule */
  PfRule d_rule = PfRule::UNKNOWN;
  /** Assumptions used as premise for this proof step */
  std::vector<Node> d_premise;
  /** Arguments for this proof step */
  std::vector<Node> d_args;
  /** Conclusion of this proof step */
  Node d_proven;
  /** Children of this proof step */
  std::vector<TreeProofNode> d_children;
};
}  // namespace detail

/**
 * This class supports the lazy creation of a tree-shaped proof.
 * The core idea is that the lazy creation is necessary because proof rules
 * depend on assumptions that are only known after the whole subtree has been
 * finished.
 *
 * We indend to argue about proofs that roughly go as follows:
 * - we assume a set of assumptions
 * - we do a case split
 * - for every case, we derive false, possibly by nested case splits
 *
 * Every case is represented by a SCOPE whose child derives false. When
 * composing the final proof, we explicitly extend the premise of every proof
 * step with the scope (the currently selected case) that this proof step lives
 * in. When doing this, we ignore the outermost scope (which assumes the
 * assertion set) to allow for having conflicts that are only a subset of the
 * assertion set.
 *
 * Consider the example  x*x<1 and x>2  and the intended proof
 *  (SCOPE
 *    (ARITH_NL_COVERING_RECURSIVE
 *      (SCOPE
 *        (ARITH_NL_COVERING_DIRECT  (x<=2  and  x>2) ==> false)
 *        :args [x<=2]
 *      )
 *      (SCOPE
 *        (ARITH_NL_COVERING_DIRECT  (x>=1  and  x*x<1) ==> false)
 *        :args [x>=1]
 *      )
 *    )
 *    :args [ x*x<1, x>2 ]
 *  )
 * We obtain this proof in a way that (in general) gives us the assumptions
 * for the scopes (x<=2, x>=1) only when the scope children have been fully
 * computed. Thus, we store the proof in an intermediate form and add the scope
 * arguments when we learn them. Once we have completed the proof, we can easily
 * transform it into proper ProofNodes.
 *
 * This class is stateful in the sense that the interface (in particular
 * openChild() and closeChild()) navigates the proof tree (and creating it
 * on-the-fly). Initially, and after reset() has been called, the proof consists
 * of one empty proof node (with proof rule UNKNOWN). It stores the current
 * position in the proof tree internally to make the interface easier to use.
 *
 * THIS MAKES THIS CLASS INHERENTLY NOT THREAD-SAFE!
 *
 * To construct the above proof, use this class roughly as follows:
 *  setCurrent(SCOPE, {}, assertions, false);
 *  openChild();
 *  // First nested scope
 *  openChild();
 *  setCurrent(SCOPE, {}, {}, false);
 *  openChild();
 *  setCurrent(ARITH_NL_COVERING_DIRECT, {x>2}, {}, false);
 *  closeChild();
 *  getCurrent().args = {x<=2};
 *  closeChild();
 *  // Second nested scope
 *  openChild();
 *  setCurrent(SCOPE, {}, {}, false);
 *  openChild();
 *  setCurrent(ARITH_NL_COVERING_DIRECT, {x*x<1}, {}, false);
 *  closeChild();
 *  getCurrent().args = {x>=1};
 *  closeChild();
 *  // Finish split
 *  setCurrent(ARITH_NL_COVERING_RECURSIVE, {}, {}, false);
 *  closeChild();
 *  closeChild();
 *
 * To explicitly finish proof construction, we need to call closeChild() one
 * additional time.
 */
class LazyTreeProofGenerator : protected EnvObj, public ProofGenerator
{
 public:
  friend std::ostream& operator<<(std::ostream& os,
                                  const LazyTreeProofGenerator& ltpg);

  LazyTreeProofGenerator(Env& env,
                         const std::string& name = "LazyTreeProofGenerator");

  std::string identify() const override { return d_name; }
  /** Create a new child and make it the current node */
  void openChild();
  /**
   * Finish the current node and return to its parent
   * Checks that the current node has a proof rule different from UNKNOWN.
   * When called on the root node, this finishes the proof construction: we can
   * no longer call getCurrent(), setCurrent() openChild() and closeChild(), but
   * instead can call getProof() now.
   */
  void closeChild();
  /**
   * Return a reference to the current node
   */
  detail::TreeProofNode& getCurrent();
  /** Set the current node / proof step */
  void setCurrent(size_t objectId,
                  PfRule rule,
                  const std::vector<Node>& premise,
                  std::vector<Node> args,
                  Node proven);
  /** Construct the proof as a ProofNode */
  std::shared_ptr<ProofNode> getProof() const;
  /** Return the constructed proof. Checks that we have proven f */
  std::shared_ptr<ProofNode> getProofFor(Node f) override;
  /** Checks whether we have proven f */
  bool hasProofFor(Node f) override;

  /**
   * Removes children from the current node based on the given predicate.
   * It can be used for cases where facts (and their proofs) are eagerly
   * generated and then later pruned, for example to produce smaller conflicts.
   * The predicate is given as a Callable f that is called for every child with
   * the id of the child and the child itself.
   * f should return false if the child should be kept, true if the child should
   * be removed.
   * @param f a Callable bool(std::size_t, const detail::TreeProofNode&)
   */
  template <typename F>
  void pruneChildren(F&& f)
  {
    auto& children = getCurrent().d_children;

    auto it =
        std::remove_if(children.begin(), children.end(), std::forward<F>(f));
    children.erase(it, children.end());
  }

 private:
  /** recursive proof construction used by getProof() */
  std::shared_ptr<ProofNode> getProof(
      std::vector<std::shared_ptr<ProofNode>>& scope,
      const detail::TreeProofNode& pn) const;

  /** recursive debug printing used by operator<<() */
  void print(std::ostream& os,
             const std::string& prefix,
             const detail::TreeProofNode& pn) const;

  /** The trace to the current node */
  std::vector<detail::TreeProofNode*> d_stack;
  /** The root node of the proof tree */
  detail::TreeProofNode d_proof;
  /** Caches the result of getProof() */
  mutable std::shared_ptr<ProofNode> d_cached;
  /** Name of this proof generator */
  std::string d_name;
};

/**
 * Prints the current state of a LazyTreeProofGenerator. Can also be used on a
 * partially constructed proof. It is intended for debugging only and attempts
 * to pretty-print itself using indentation.
 */
std::ostream& operator<<(std::ostream& os, const LazyTreeProofGenerator& ltpg);

}  // namespace cvc5::internal

#endif
