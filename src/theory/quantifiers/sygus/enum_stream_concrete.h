/*********************                                                        */
/*! \file enum_stream_concrete.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief class for streaming concrete values from enumerated abstract ones
 **/
#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__SYGUS__ENUM_STREAM_CONCRETE_H
#define __CVC4__THEORY__QUANTIFIERS__SYGUS__ENUM_STREAM_CONCRETE_H

#include "expr/node.h"
#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/sygus/synth_conjecture.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

// TODO stream values by replacing, for each permutation, the ordered subsets of
// different variables

class StreamPermutation
{
 public:
  StreamPermutation(Node value,
                    const std::vector<std::vector<Node>>& var_classes,
                    TermDbSygus* tds);
  Node getNextPermutation();

 private:
  /** value to which we are generating permutations */
  Node d_value;
  /** all variables of value */
  std::vector<Node> d_vars;
  /** generated permutations (modulo rewriting) */
  std::unordered_set<Node, NodeHashFunction> d_perm_values;
  /** sygus term database */
  TermDbSygus* d_tds;
  /** Heap's algorithm for permutation */
  class PermutationState
  {
   public:
    PermutationState(const std::vector<Node>& vars);
    void getLastPermutation(std::vector<Node>& perm);

    bool getNextPermutation(std::vector<Node>& perm);

   private:
    std::vector<Node> d_vars;
    std::vector<Node> d_last_perm;
    std::vector<unsigned> d_seq;
    unsigned d_curr_ind;
  };
  /** permutation state of each variable class */
  std::vector<PermutationState> d_perm_state_class;
};

class EnumStreamConcrete
{
 public:
  EnumStreamConcrete(QuantifiersEngine* qe, SynthConjecture* p);
  ~EnumStreamConcrete() {}
  /** register enumerator for this class
   *
   * during registration builds a map from the variables of e's type to their
   * type classes
   */
  void registerEnumerator(Node e);
  /** register abstract value v */
  void registerAbstractValue(Node v);
  /** retrieve next value
   *
   * if no more permutations exist from the last registered value, this method
   * returns Node::null()
   */
  Node getNext();

 private:
  /** reference to quantifier engine */
  QuantifiersEngine* d_qe;
  /** sygus term database of d_qe */
  quantifiers::TermDbSygus* d_tds;
  /** reference to the parent conjecture */
  SynthConjecture* d_parent;
  /** enumerator we are concretizing values for */
  Node d_enum;
  /** list of registered abstract values */
  std::vector<Node> d_abs_values;
  std::vector<StreamPermutation> d_stream_permutations;
  /** maps variables to ids of their respective type classes */
  std::map<Node, unsigned> d_var_class;
  /** retrieve valiables occurring in value */
  void collectVars(Node n,
                   std::vector<Node>& vars,
                   std::unordered_set<Node, NodeHashFunction>& visited);
  void splitVarClasses(const std::vector<Node>& vars,
                       std::vector<std::vector<Node>>& var_classes);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif
