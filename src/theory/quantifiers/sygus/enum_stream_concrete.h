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
#include "theory/quantifiers/sygus/synth_conjecture.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class StreamPermutation
{
 public:
  StreamPermutation(Node value,
                    const std::vector<Node>& perm_vars,
                    const std::vector<std::vector<Node>>& var_classes,
                    TermDbSygus* tds);
  /** compute next permutation, if any, of value
   *
   * a "next" permutation is determined by having at one new permutation in one
   * of the variable type classes in the value.
   *
   * For example, if the variables of value (OP x1 x2 x3 x4) are partioned into
   * {{x1, x4}, {x2, x3}} then the sequence of getNext() is
   *
   * (OP x4 x2 x3 x1)
   *
   * Moreover, new values are only considered if they are unique modulo
   * rewriting. If for example OP were "+", then no next value would exist,
   * while if OP were "-" the next values would be
   *
   * (- x4 ...)

   */
  Node getNext();
  /** retrieve last permutation */
  Node getLast();

 private:
  /** value to which we are generating permutations */
  Node d_value;
 /** last value generated */
  Node d_last_value;
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

    void reset();
    bool getNextPermutation();

    std::vector<Node> d_vars;
    std::vector<Node> d_last_perm;

   private:
    std::vector<unsigned> d_seq;
    unsigned d_curr_ind;
  };
  /** permutation state of each variable class */
  std::vector<PermutationState> d_perm_state_class;
  /** current class being permuted */
  unsigned d_curr_ind;
};

// TODO need to have the same handling of type classes as above
class StreamCombination
{
 public:
  StreamCombination(Node value,
                    const std::map<Node, std::vector<Node>>& var_cons,
                    const std::vector<Node>& all_vars,
                    const std::vector<std::vector<Node>>& all_var_classes,
                    const std::vector<Node>& perm_vars,
                    const std::vector<std::vector<Node>>& perm_var_classes,
                    TermDbSygus* tds);
  Node getNext();

 private:
  Node d_last;
  /** all variables */
  std::vector<Node> d_all_vars;
  std::vector<Node> d_perm_vars;
  std::map<Node, std::vector<Node>> d_var_cons;
  /** generated combinations (for debugging) */
  std::unordered_set<Node, NodeHashFunction> d_comb_values;
  /** sygus term database */
  TermDbSygus* d_tds;

  StreamPermutation d_stream_permutations;
  /** Heap's algorithm for permutation */
  class CombinationState
  {
   public:
    CombinationState(unsigned n, unsigned k, const std::vector<Node>& vars);

    bool getNextCombination();

    void reset();
    void getLastVars(std::vector<Node>& vars);

   private:
    unsigned d_n, d_k;
    std::vector<unsigned> d_last_comb;
    std::vector<Node> d_vars_class;
  };
  /** combination state */
  std::vector<CombinationState> d_comb_state_class;
  /** current class being combined */
  unsigned d_curr_ind;
};

/** Streamer of concrete values for enumerator
 *
 * When a given enumerator is "variable agnostic", only values in which
 * variables are ordered are chosen for it (see
 * TermDbSygus::registerEnumerator). If such values are seen as "abstract", in
 * the sense that each represent a set of values, this class can be used to
 * stream all the concrete values that correspond to them.
 *
 * For example a variable agnostic enumerator that contains three variables, x1,
 * x2, x3, in which x1 < x2 < x3, for which an "abstract" value (OP x1 x2) is
 * derived, will lead to the stream of "concrete" values
 *
 * (OP x1 x2)
 * (OP x1 x3)
 * (OP x2 x3)
 *
 * (OP x2 x1)
 * (OP x3 x1)
 * (OP x3 x2)
 *
 * in which for each permutation of the variables in the abstract value
 * ([x1, x2] and [x2, x1] in the above) we generate all the ordered combinations
 * of the variables of the enumerator ([x1, x2], [x1, x3], and [x2, x3] in the
 * above).
 *
 * Moreover the permutations are generated modulo rewriting, s.t. if two
 * permutations are equivalent, only one is used.
 *
 * It should be noted that the variables of a variable agnostic enumerator are
 * kept in independent "type classes" (see TermDbSygus::getSubclassForVar).
 * Therefore when streaming concrete values permutatinos and combinations are
 * generated by the product of the permutatinos and combinations of each class.
 */
class EnumStreamConcrete
{
 public:
  EnumStreamConcrete(QuantifiersEngine* qe, SynthConjecture* p);
  ~EnumStreamConcrete() {}
  /** register enumerator for this class
   *
   * during registration builds a map from the variables of the enumerator's
   * type to their type classes
   */
  void registerEnumerator(Node e);
  /** register abstract value v
   *
   * during registration collects variables occurring in value and sets up
   * utilities for streaming combinatinos and permutations for building concrete
   * values
   */
  void registerAbstractValue(Node v);
  /** generate next concrete value
   *
   * if no more combinations / permutations exist from the last registered
   * value, this method returns Node::null()
   */
  Node getNext();

 private:
  /** reference to quantifier engine */
  QuantifiersEngine* d_qe;
  /** reference to the parent conjecture */
  SynthConjecture* d_parent;
  /** sygus term database of d_qe */
  quantifiers::TermDbSygus* d_tds;
  /** enumerator we are concretizing values for */
  Node d_enum;
  /** variables from enumerator's type */
  std::vector<Node> d_vars;
  /** partition of variables per type classes */
  std::vector<std::vector<Node>> d_var_classes;
  /** maps variables to their respective constructors in all the enumerator
   * sutypes */
  std::map<Node, std::vector<Node>> d_var_cons;
  /** list of registered abstract values */
  std::vector<Node> d_abs_values;
  /** combination utils of registered values */
  std::vector<StreamCombination> d_stream_combinations;
  /** maps variables to ids of their respective type classes */
  std::map<Node, unsigned> d_var_class;
  /** retrieve valiables occurring in value */
  void collectVars(Node n,
                   std::vector<Node>& vars,
                   std::unordered_set<Node, NodeHashFunction>& visited);
  /** partition variable set according to different type classes */
  void splitVarClasses(const std::vector<Node>& vars,
                       std::vector<std::vector<Node>>& var_classes);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif
