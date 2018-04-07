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

#ifndef __CVC4__THEORY__SYMMETRY_DETECT_H
#define __CVC4__THEORY__SYMMETRY_DETECT_H

#include <map>
#include <string>
#include <vector>
#include "expr/node.h"

namespace CVC4 {

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
   * This is the class to store the partition,
   * where d_term store the term corresponding to the partition,
   * d_var_to_subvar is the mapping from the variable to the substitution
   * variable, and d_subvar_to_vars is the mapping from the substitution
   * variable to a list of variables forming a region of a partition.
   */
  class Partition
  {
   public:
    /** Term corresponding to the partition, e.g., x + y = 0 */
    Node d_term;
    /** Mapping between the variable and the substitution variable x -> w, y -> w,
     * z -> w */
    std::map<Node, Node> d_var_to_subvar;

    /** Mapping between the substitution variable and variables w-> { x, y, z } */
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
    void getNewPartition(Partition& part);
    void getNewPartition(Partition& part, PartitionTrie& pt);
  };


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
  void collectChildren(Node node, Kind k, std::vector<Node>& children);

  /** Print a partition */
  void printPartition(Partition p);

  /** Retrieve all variables from partitions and put in vars */
  void getVariables(std::vector<Partition>& partitions,
                    std::unordered_set<Node, NodeHashFunction>& vars);

  /** Process singleton partitions and add all variables to vars
   *  It collects all partitions with more than 1 variable and save it in
   *  partitions first. And then it collects the substitution variable to
   *  variable and to term mappings respectively from partitions with 1
   *  variable and invokes matches function on the mappings to check
   *  if any subset of the variables can be merged. If yes, they will be merged
   *  and put in partitions. The remaining ones after the merge check will be
   *  put in the partitions as well.
   * */
  void processSingletonPartitions(std::vector<Partition>& partitions,
                                  std::unordered_set<Node, NodeHashFunction>& vars);

  /** Do matches on singleton partitions
   *  This function checks if any subset of the expressions corresponding to
   *  substitution variables are equivalent under variables substitution.
   *  If the expressions are equivalent, we will merge the variables corresponding
   *  to the same substitution variables and put them in partitions.
   *  For example, suppose we have subvar_to_var: {w1 -> u, w2 -> x, w3 -> y,
   *  w4 -> z} and subvar_to_expr: {w1 -> u>2, w2 -> x>0, w3 -> y>0, w4 -> z>1}.
   *  Since [x/w]>0 is equivalent [y/w]>0 but not equivalent to [z/w]>1 and [u/w]>2,
   *  and [u/w]>2 is not equivalent to [z/w]>1, we would merge x and y and put
   *  w5->{x, y} and also w1->{u}, w4->{z} in partitions.
   * */
  void matches(std::vector<Partition>& partitions,
               std::map<Node, Node>& subvar_to_var,
               std::map<Node, Node>& subvar_to_expr);
};

}  // namespace CVC4

#endif
