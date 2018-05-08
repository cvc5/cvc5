/*********************                                                        */
/*! \file symmetry_detect.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Paul Meng, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Symmetry detection for theories
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PREPROCESSING__PASSES__SYMMETRY_DETECT_H
#define __CVC4__PREPROCESSING__PASSES__SYMMETRY_DETECT_H

#include <map>
#include <string>
#include <vector>
#include "expr/node.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

/**
 * This is the class to detect symmetries from input based on terms equality.
 * */
class SymmetryDetect
{
 public:
  /**
   * Constructor
   * */
  SymmetryDetect()
  {
    d_trueNode = NodeManager::currentNM()->mkConst<bool>(true);
    d_falseNode = NodeManager::currentNM()->mkConst<bool>(false);
  }

  /**
   * Destructor
   * */
  ~SymmetryDetect() {}

  /** Get the final partition after symmetry detection.
   *  If a vector in parts contains two variables x and y,
   *  then assertions and assertions { x -> y, y -> x } are
   *  equisatisfiable.
   * */
  void getPartition(std::vector<std::vector<Node> >& parts, const std::vector<Node>& assertions);

 private:
  /**
   * This is the class stores a "partition", which is a way of representing a
   * class of symmetries.
   * 
   * For example, when finding symmetries for a term like x+y = 0, we 
   * construct a partition { w -> { x, y } } that indicates that automorphisms
   * over { x, y } do not affect the satisfiability of this term. In this
   * example, we have the following assignments to the members of this class:
   *   d_term : x+y=0
   *   d_sterm : w+w=0
   *   d_var_to_subvar : { x -> w, y -> w }
   *   d_subvar_to_vars : { w -> { x, y } }
   * We often identify a partition with its d_subvar_to_vars field.
   * 
   * We call w a "symmetry breaking variable". 
   */
  class Partition
  {
   public:
    /** The term for which the partition was computed for. */
    Node d_term;
    /** Substituted term corresponding to the partition 
     * 
     * This is equal to d_term * d_var_to_subvar, where * is application of 
     * substitution.
     */
    Node d_sterm;
    /** 
     * Mapping between the variable and the symmetry breaking variable e.g. 
     * { x -> w, y -> w }.
     */
    std::map<Node, Node> d_var_to_subvar;

    /** 
     * Mapping between the symmetry breaking variables and variables, e.g.
     * { w-> { x, y } } 
     */
    std::map<Node, std::vector<Node> > d_subvar_to_vars;
  };

  /**
   * We build the partition trie indexed by
   * parts[0].var_to_subvar[v]....parts[n].var_to_subvar[v]. The leaves of a
   * partition trie is the new regions of a partition
   */
  class PartitionTrie
  {
   public:
    /** Variables at the leave */
    std::vector<Node> d_variables;

    /** The mapping from a node to its children */
    std::map<Node, PartitionTrie> d_children;

    /** Add variable v to the trie, indexed by
     * parts[0].var_to_subvar[v]....parts[n].var_to_subvar[v]. */
    void addNode(Node v, std::vector<Partition>& parts);
    void addNode(Node v, std::vector<Node>& subs);

    /** Get all the new regions of a partition and store in part */
    void getNewPartition(Partition& part, PartitionTrie& pt);
  };
  /** (canonical) symmetry breaking variables for each type */
  std::map<TypeNode, std::vector<Node> > d_sb_vars;
  /** 
   * Get the index^th symmetry breaking variable for type tn in the above 
   * vector. These are fresh variables of type tn which are used for
   * constructing a canonical form for terms considered by this class, and
   * are used in the domains of partitions (Partition::d_subvar_to_vars).
   */
  Node getSymBreakVariable(TypeNode tn, unsigned index);

  /** True and false constant nodes */
  Node d_trueNode;
  Node d_falseNode;

  /** Cache for partitions */
  std::map<Node, Partition> d_term_partition;

  /** detect
   *
   * Called on the input assertions, where assertions are interpreted as a
   * conjunction. This computes a partition P of the variables in assertions
   * such that for each set S in P, then all automorphisms for S applied to
   * assertions result in an equisatisfiable formula.
   */
  Partition detect(const std::vector<Node>& assertions);

  /** Find symmetries in node */
  SymmetryDetect::Partition findPartitions(Node node);

  /** Collect children of a node
   *  If the kind of node is associative, we will chain its children together.
   *  We might need optimizations here, such as rewriting the input to negation
   *  normal form.
   * */
  void collectChildren(Node node, std::vector<Node>& children);

  /** Print a partition */
  void printPartition(const char* c, Partition p);

  /** merge partitions
   *
   * This method is called when we have detected symmetries for the children
   * of a term t of the form <k>( t_1, ..., t_n ), where k is a commutative
   * operator. For each i=1,...n, partitions[i] represents symmetries (in the
   * form of a partition) computed for the child t_i.
   *
   * The vector indices stores a list ( i_1...i_m ) such that
   * ( t_i_j * partition[i_j].d_var_to_subvar ) is syntactically equivalent
   * for each j=1...m, where * is application of substitution.
   *
   * This method tries to "merge" partitions for a subset of these children.
   * We say that
   *   partition[j1] = { w -> X_1 },
   *   ...,
   *   partition[jp] = { w -> X_p }
   * are mergebale if s=|X_1|=...=|X_p|, and all subsets X of
   * X* = ( union_{k=1...p} X_k ) of size s are equal to exactly one of
   * X_1 ... X_p. If there exists a mergeable set of partitions with indices
   * (j1...jp), we remove {j1...jp} \ { j1 } from active_indices, and update
   * partition[j1] := { w -> X* }.
   */
  bool mergePartitions(Kind k,
                       std::vector<Partition>& partitions,
                       const std::vector<unsigned>& indices,
                       std::unordered_set<unsigned>& active_indices);
  /** merge partitions
   *
   * This is a recursive helper for the above function. This function attempts
   * to construct a set of mergebale indices {j1...jp} of partitions.
   *
   * include_indices : the currently considered indices {j1...jp},
   * curr_index : the index we are currently considering whether to add to
   * include_indices,
   * curr_variables : the current set X*,
   * num_vars : the size of the range of partitions, i.e. |X_i| above.
   */
  bool mergePartitions(
      Kind k,
      std::unordered_set<unsigned>& include_indices,
      unsigned curr_index,
      std::unordered_set<Node, NodeHashFunction>& curr_variables,
      unsigned num_vars,
      std::vector<Partition>& partitions,
      const std::vector<unsigned>& indices,
      std::unordered_set<unsigned>& active_indices);
  /** mk commutative node
   *
   * This returns (a normal form for) the term <k>( children ), where
   * k is a commutative operator. We return a right-associative chain,
   * since some commutative operators (e.g. set union) require this.
   */
  Node mkCommutativeNode(Kind k, std::vector<Node>& children) const;
};
}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif
