/*********************                                                        */
/*! \file symmetry_detect.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Paul Meng, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Symmetry detection for theories
 **/

#include "cvc4_private.h"

#ifndef __CVC4__SYMMETRY_DETECT_H
#define __CVC4__SYMMETRY_DETECT_H

#include <iostream>
#include <map>
#include <string>
#include <vector>
#include "expr/node.h"
#include "expr/type_node.h"

using namespace std;

namespace CVC4 {

/**
 * This is the class to detect symmetries from input based on terms equality.
 * */
class SymmetryDetect
{
 public:
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
    /** Mapping between the variable and the substitute variable x -> w, y -> w,
     * z -> w */
    std::map<Node, Node> d_var_to_subvar;

    /** Mapping between the substitute variable and variables w-> { x, y, z } */
    std::map<Node, vector<Node> > d_subvar_to_vars;
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
    void addNode(Node v, vector<Partition>& parts);
    void addNode(Node v, vector<Node>& subs);

    /** Get all the new regions of a partition and store in part */
    void getNewPartition(Partition& part);
    void getNewPartition(Partition& part, PartitionTrie& pt);
  };

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

  /** detect
   *
   * Called on the input assertions, where assertions are interpreted as a
   * conjunction. This computes a partition P of the variables in assertions
   * such that for each set S in P, then all automorphisms for S applied to
   * assertions result in an equisatisfiable formula.
   */
  Partition detect(vector<Node>& assertions);

  /** Get the final partition after symmetry detection */
  void getPartition(vector<vector<Node> >& parts, vector<Node>& assertions);

  /** Pretty print a vector of nodes */
  static string printNodeVector(vector<Node> nodes);

  /** Pretty print a set of nodes */
  static string printNodeSet(unordered_set<Node, NodeHashFunction> nodes);

 private:
  /** True and false constant nodes */
  Node d_trueNode;
  Node d_falseNode;

  /** Cache for partitions */
  std::map<Node, Partition> d_term_partition;

  /** Find symmetries in node */
  SymmetryDetect::Partition findPartitions(Node node);

  /** Collect children of a node
   *  If the kind of node is associative, we will chain its children together.
   *  We might need optimizations here, such as rewriting the input to negation
   * normal form.
   * */
  void collectChildren(Node node, vector<Node>& children);
  void collectChildren(Node node, Kind k, vector<Node>& children);

  /** Print a partition */
  void printPartition(Partition p);

  /** Get all variables from partitions */
  void getVariables(vector<Partition>& partitions,
                    unordered_set<Node, NodeHashFunction>& vars);

  /** Process singleton partitions and add all variables to vars */
  void processSingletonPartitions(vector<Partition>& partitions,
                                  unordered_set<Node, NodeHashFunction>& vars);

  /** Do matches on singleton partitions */
  void matches(vector<Partition>& partitions,
               map<Node, Node>& subvar_to_var,
               map<Node, Node>& subvar_to_expr);
};

}  // namespace CVC4

#endif
