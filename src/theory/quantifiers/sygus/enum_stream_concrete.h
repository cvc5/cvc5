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

class EnumStreamConcrete;

/** Streamer of different values according to variable permutations
 *
 * Generates a new value (modulo rewriting) when queried in which its variables
 * are permuted.
 */
class StreamPermutation
{
 public:
  /** initializes utility
   *
   * for each subset of the variables in value (according to the subclasses
   * defined in the partition var_classes), a permutation utility is initialized
   */
  StreamPermutation(Node value, EnumStreamConcrete* esc);
  ~StreamPermutation() {}
  /** computes next permutation, if any, of value
   *
   * a "next" permutation is determined by having at least one new permutation
   * in one of the variable subclasses in the value.
   *
   * For example, if the variables of value (OP x1 x2 x3 x4) are partioned into
   * {{x1, x4}, {x2, x3}} then the sequence of getNext() is
   *
   * (OP x4 x2 x3 x1)
   * (OP x1 x3 x2 x4)
   * (OP x4 x3 x2 x1)
   *
   * Moreover, new values are only considered if they are unique modulo
   * rewriting. If for example OP were "+", then no next value would exist,
   * while if OP were "-" the only next value would be: (- x4 x2 x3 x1)
   */
  Node getNext();

  /** all variables of value */
  std::vector<Node> d_vars;
  std::vector<std::vector<Node>> d_var_classes;

private:
  /** whether first query */
  bool d_first;
  /** parent streaming utility */
  EnumStreamConcrete* d_esc;
  /** value to which we are generating permutations */
  Node d_value;
  /** generated permutations (modulo rewriting) */
  std::unordered_set<Node, NodeHashFunction> d_perm_values;
  /** retrieves variables occurring in value */
  void collectVars(Node n,
                   std::vector<Node>& vars,
                   std::unordered_set<Node, NodeHashFunction>& visited);
  /** Utility for stepwise application of Heap's algorithm for permutation
   *
   * see https://en.wikipedia.org/wiki/Heap%27s_algorithm
   */
  class PermutationState
  {
   public:
    PermutationState(const std::vector<Node>& vars);
    /** computes next permutation, i.e. execute one step of Heap's algorithm
     *
     * returns true if one exists, false otherwise
     *
     * when a new permutation is generated the the new variable arrangement is
     * stored in d_last_perm
     */
    bool getNextPermutation();
    /** resets permutation state to initial variable ordering */
    void reset();
    /** variables being permuted */
    std::vector<Node> d_vars;
    /** last computed permutation of variables */
    std::vector<Node> d_last_perm;

   private:
    /** auxiliary position list for generating permutations */
    std::vector<unsigned> d_seq;
    /** current index being permuted */
    unsigned d_curr_ind;
  };
  /** permutation state of each variable subclass */
  std::vector<PermutationState> d_perm_state_class;
  /** current variable subclass being permuted */
  unsigned d_curr_ind;
};

/** Streamer of different values according to variable combinations and
 * permutations
 *
 * Generates a new value when queried in which a new ordered combination of
 * variables is used. When all combinations are exhausted, a new base value is
 * generated in which its variables are permuted (if any such new value exist
 * modulo rewriting), and the cycle restarts.
 */
class StreamCombination
{
 public:
  /** initializes utility
   *
   * the combinations are generated from a initial set of variables (the union
   * of d_vars_classes in the parent EnumStreamConcrete) from which we choose a
   * subset of variables in the same quantity as those occurring in the given
   * value.
   *
   * The combinations are performed modulo subclasses. For each subclass of the
   * given variables, a combination utility is initialized.
   */
  StreamCombination(Node value, EnumStreamConcrete* esc);
  ~StreamCombination() {}
  /** computes next combination, if any, of value
   *
   * a "next" combination is determined by having at least one new combination
   * in one of the variable subclasses in the initial set of variables. If no
   * new combination exist, the cycle restarts with a new base value generated
   * by StreamPermutation::getNext() (see above).
   *
   * This layered approach (of deriving all combinations for each permutation)
   * allows the generation of ordered combinations. See the example in
   * EnumStreamConcrete for further details.
   *
   * Since the same variable can occur in different subfield types (and
   * therefore their datatype equivalents would have different types) a map from
   * variable to set of constructors (var_cons) is used to build substitutions
   * in a proper way when generating different combinations.
   */
  Node getNext();

 private:
  /** parent streaming utility */
  EnumStreamConcrete* d_esc;
  /** last value generated after a combination
   *
   * If getNext() has been called, this is the return value of the most recent
   * call to getNext(). Otherwise, this value is null.
   */
  Node d_last;
  /** generated combinations (for debugging) */
  std::unordered_set<Node, NodeHashFunction> d_comb_values;
  /** permutation utility */
  StreamPermutation d_stream_permutations;
  /** Utility for stepwise generation of ordered subsets of size k from n
   * variables */
  class CombinationState
  {
   public:
    CombinationState(unsigned n, unsigned k, const std::vector<Node>& vars);
    /** computes next combination
     *
     * returns true if one exists, false otherwise
     */
    bool getNextCombination();
    /** resets combination state to first k variables in vars */
    void reset();
    /** retrieves last variable combination
     *
     * variables in new combination are stored in argument vars
     */
    void getLastComb(std::vector<Node>& vars);

   private:
    /** number of variables */
    unsigned d_n;
    /** size of subset */
    unsigned d_k;
    /** last combination state */
    std::vector<unsigned> d_last_comb;
    /** variables from which combination is extracted */
    std::vector<Node> d_vars;
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
 * kept in independent "subclasses" (see TermDbSygus::getSubclassForVar).
 * Therefore when streaming concrete values permutations and combinations are
 * generated by the product of the permutations and combinations of each class.
 */
class EnumStreamConcrete
{
 public:
  EnumStreamConcrete(quantifiers::TermDbSygus* tds);
  ~EnumStreamConcrete() {}
  /** initializes class with the given enumerator
   *
   * during initialization builds a map from the variables of the enumerator's
   * type to their (type) subclasses
   */
  void initialize(Node e);
  /** registers abstract value v
   *
   * during registration collects variables occurring in value and sets up
   * utilities for streaming combinations and permutations for building concrete
   * values
   */
  void registerAbstractValue(Node v);
  /** generates next concrete value
   *
   * if no more combinations / permutations exist from the last registered
   * value, this method returns Node::null()
   */
  Node getNext();
  /** partition of variables per subclasses */
  std::vector<std::vector<Node>> d_var_classes;
  /** maps variables to their respective constructors in all the enumerator
   * subfield types */
  std::map<Node, std::vector<Node>> d_var_cons;
  /** partitions variable set according to different subclasses */
  void splitVarClasses(const std::vector<Node>& vars,
                       std::vector<std::vector<Node>>& var_classes);
  /** sygus term database of current quantifiers engine */
  quantifiers::TermDbSygus* d_tds;

 private:
  /** enumerator we are concretizing values for */
  Node d_enum;
  /** last registered abstract value */
  Node d_abs_value;
  /** variables from enumerator's type */
  std::vector<Node> d_vars;
  /** combination util for registered value */
  std::unique_ptr<StreamCombination> d_stream_combination;
  /** maps variables to ids of their respective subclasses */
  std::map<Node, unsigned> d_var_class;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif
