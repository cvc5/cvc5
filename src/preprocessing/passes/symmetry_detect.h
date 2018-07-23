/*********************                                                        */
/*! \file symmetry_detect.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Paul Meng
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
namespace symbreak {

/**
 * This class stores a "partition", which is a way of representing a
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
  /** sorts the ranges of d_subvar_to_vars. */
  void normalize();
  /** Print a partition */
  static void printPartition(const char* c, Partition p);
};

/** partition merger
 *
 * This class is used to identify sets of children of commutative operators k
 * that are identical up to a set of automorphisms.
 *
 * This class is used when we have detected symmetries for the children
 * of a term t of the form <k>( t_1, ..., t_n ), where k is a commutative
 * operator. For each i=1,...n, partitions[i] represents symmetries (in the
 * form of a partition) computed for the child t_i.
 *
 * The vector d_indices of this class stores a list ( i_1...i_m ) such that
 * ( t_i_j * partition[i_j].d_var_to_subvar ) is syntactically equivalent
 * for each j=1...m, where * is application of substitution.
 *
 * In detail, we say that
 *   partition[j1] = { w -> X_1 },
 *   ...,
 *   partition[jp] = { w -> X_p }
 * are mergeable if s=|X_1|=...=|X_p|, and all subsets of
 * X* = ( union_{k=1...p} X_k ) of size s are equal to exactly one of
 * X_1 ... X_p.
 */
class PartitionMerger
{
 public:
  PartitionMerger()
      : d_kind(kind::UNDEFINED_KIND),
        d_master_base_index(0),
        d_num_new_indices_needed(0)
  {
  }
  /** initialize this class
   *
   * We will be trying to merge the given partitions that occur at the given
   * indices. k is the kind of the operator that partitions are children of.
   */
  void initialize(Kind k,
                  const std::vector<Partition>& partitions,
                  const std::vector<unsigned>& indices);
  /** merge
   *
   * This method tries to "merge" partitions occurring at the indices d_indices
   * of the vector partitions.
   *
   * Assuming the setting described above, if there exists a mergeable set of
   * partitions with indices (j_m1...j_mp), we remove {j_m1...j_mp} \ { j_m1 }
   * from active_indices, and update partition[j1] := { w -> X* }.
   *
   * The base_index is an index from d_indices that serves as a basis for
   * detecting this symmetry. In particular, we start by assuming that
   * p=1, and j_m1 is base_index. We proceed by trying to find sets of indices
   * that add exactly one variable to X* at a time. We return
   * true if p>1, that is, at least one partition was merged with the
   * base_index.
   */
  bool merge(std::vector<Partition>& partitions,
             unsigned base_index,
             std::unordered_set<unsigned>& active_indices);

 private:
  /** the kind of the node we are consdiering */
  Kind d_kind;
  /** indices we are considering */
  std::vector<unsigned> d_indices;
  /** count the number of times each variable occurs */
  std::map<Node, unsigned> d_occurs_count;
  /** the number of times each variable occurs up to the given index */
  std::map<unsigned, std::map<Node, unsigned> > d_occurs_by;
  /** current master base index */
  unsigned d_master_base_index;
  /** the indices that occur in the current symmetry (the list (j1...jp)) */
  std::unordered_set<unsigned> d_base_indices;
  /** the free variables that occur in the current symmetry (the set X*)*/
  std::unordered_set<Node, NodeHashFunction> d_base_vars;
  /** the number of indices we need to add to extended X* by one variable */
  unsigned d_num_new_indices_needed;
  /** the variables we have currently tried to add to X* */
  std::unordered_set<Node, NodeHashFunction> d_merge_var_tried;
  /** merge new variable
   *
   * This is a recursive helper for the merge function. This function attempts
   * to construct a set of indices {j1...jp} of partitions and a variable
   * "merge_var" such that partitions[ji] is of the form { w -> X_ji }, where
   * merge_var in X_ji and ( X_ji \ { merge_var } ) is a subset of the base
   * variables X*. We require that p = d_num_new_indices_needed, where
   * d_num_new_indices_needed is
   *   |d_base_vars| choose (|X_ji|-1)
   * that is, n!/((n-k)!*k!) where n=|d_base_vars| and k=|X_ji|-1.
   *
   * curr_index : the index of d_indices we are currently considering whether
   * to add to new_indices,
   * new_indices : the currently considered indices {j1...jp},
   * merge_var : the variable we are currently trying to add to X*,
   * new_merge_var_max : the maximum number of times that merge_var might
   * appear in remainding indices, i.e. d_indices[curr_index]...d_indices.end(),
   * which is used as an optimization for recognizing quickly when this method
   * will fail.
   */
  bool mergeNewVar(unsigned curr_index,
                   std::vector<unsigned>& new_indices,
                   Node& merge_var,
                   unsigned num_merge_var_max,
                   std::vector<Partition>& partitions,
                   std::unordered_set<unsigned>& active_indices);
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
  Node addNode(Node v, std::vector<Partition>& parts);

  /** Get all the new regions of a partition and store in part
   *
   * This constructs a new partition, part, where each set in this partition
   * corresponds to one leaf in the PartitionTrie pt.
   * var_to_svar: map from variables to symmetry variables to use in part.
   */
  void getNewPartition(Partition& part,
                       PartitionTrie& pt,
                       std::map<Node, Node>& var_to_svar);
};

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
  /** (canonical) symmetry breaking variables for each type */
  std::map<TypeNode, std::vector<Node> > d_sb_vars;
  /**
   * Get the index^th symmetry breaking variable for type tn in the above
   * vector. These are fresh variables of type tn which are used for
   * constructing a canonical form for terms considered by this class, and
   * are used in the domains of partitions (Partition::d_subvar_to_vars).
   * This variable is created by this method if it does not already exist.
   */
  Node getSymBreakVariable(TypeNode tn, unsigned index);
  /**
   * Get the index[tn]^th symmetry breaking variable for type tn using the
   * above function and increment index[tn].
   */
  Node getSymBreakVariableInc(TypeNode tn, std::map<TypeNode, unsigned>& index);

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
  Partition findPartitions(Node node);

  /** Collect children of a node
   *  If the kind of node is associative, we will chain its children together.
   *  We might need optimizations here, such as rewriting the input to negation
   *  normal form.
   * */
  void collectChildren(Node node, std::vector<Node>& children);

  /** process partitions
   *
   * This method is called when we have detected symmetries for the children
   * of a term t of the form <k>( t_1, ..., t_n ), where k is a commutative
   * operator.  The vector indices stores a list ( i_1...i_m ) such that
   * ( t_i_j * partition[i_j].d_var_to_subvar ) is syntactically equivalent
   * for each j=1...m, where * is application of substitution. In particular,
   * ( t_i_j * partition[i_j].d_var_to_subvar ) is equal to
   * partitions[i_j].d_sterm for each j=1...m.
   *
   * This function calls mergePartitions on subsets of these indices for which
   * it is possible to "merge" (see PartitionMerger). In particular, we consider
   * subsets of indices whose corresponding partitions are of the form
   *   { w -> { x1...xn } }
   * for each n. This means that partitions like { w -> { x1 } } and
   * { w -> { x1 x2 } } are considered separately when merging.
   */
  void processPartitions(Kind k,
                         std::vector<Partition>& partitions,
                         const std::vector<unsigned>& indices,
                         std::unordered_set<unsigned>& active_indices);
  /** merge partitions
   *
   * This method merges groups of partitions occurring in indices using the
   * PartitionMerger class. Each merge updates one partition in partitions (the
   * master index of the merge) and removes a set of indices from active_indices
   * (the slave indices).
   */
  void mergePartitions(Kind k,
                       std::vector<Partition>& partitions,
                       const std::vector<unsigned>& indices,
                       std::unordered_set<unsigned>& active_indices);
};
}  // namespace symbreak
}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif
