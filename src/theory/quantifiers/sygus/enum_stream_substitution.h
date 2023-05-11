/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Class for streaming concrete values (through substitutions) from
 * enumerated abstract ones.
 */
#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS__ENUM_STREAM_SUBSTITUTION_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS__ENUM_STREAM_SUBSTITUTION_H

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/sygus/enum_val_generator.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class TermDbSygus;

/** Streamer of different values according to variable permutations
 *
 * Generates a new value (modulo rewriting) when queried in which its variables
 * are permuted (see EnumStreamSubstitution for more details).
 */
class EnumStreamPermutation : protected EnvObj
{
 public:
  EnumStreamPermutation(Env& env, TermDbSygus* tds);
  ~EnumStreamPermutation() {}
  /** resets utility
   *
   * for each subset of the variables in value (according to their
   * subclasses_classes), a permutation utility is initialized
   */
  void reset(Node value);
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
   *
   * Since the same variable can occur in different subfield types (and
   * therefore their datatype equivalents would have different types) a map from
   * variables to sets of constructors (see var_cons) is used to build
   * substitutions in a proper way when generating different combinations.
   */
  Node getNext();
  /** retrieve variables in class with given id */
  const std::vector<Node>& getVarsClass(unsigned id) const;
  /** retrieve number of variables being permuted from subclass with given id */
  unsigned getVarClassSize(unsigned id) const;

 private:
  /** sygus term database of current quantifiers engine */
  TermDbSygus* d_tds;
  /** maps subclass ids to subset of d_vars with that subclass id */
  std::map<unsigned, std::vector<Node>> d_var_classes;
  /** maps variables to subfield types with constructors for
   * the that variable, which are themselves associated with the respective
   * constructors */
  std::map<Node, std::map<TypeNode, Node>> d_var_tn_cons;
  /** whether first query */
  bool d_first;
  /** value to which we are generating permutations */
  Node d_value;
  /** generated permutations (modulo rewriting) */
  std::unordered_set<Node> d_perm_values;
  /** retrieves variables occurring in value */
  void collectVars(Node n,
                   std::vector<Node>& vars,
                   std::unordered_set<Node>& visited);
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
     * stored in d_last_perm (in terms of d_vars' indices)
     */
    bool getNextPermutation();
    /** resets permutation state to initial variable ordering */
    void reset();
    /** retrieves last variable permutation
     *
     * vars is populated with the new variable arrangement
     */
    void getLastPerm(std::vector<Node>& vars);
    /** retrieve variables being permuted */
    const std::vector<Node>& getVars() const;

   private:
    /** variables being permuted */
    std::vector<Node> d_vars;
    /** last computed permutation of variables */
    std::vector<unsigned> d_last_perm;
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
 * in which for each permutation of the variables in the abstract value ([x1,
 * x2] and [x2, x1] in the above) we generate all the substitutions through
 * ordered combinations of the variables of the enumerator ([x1, x2], [x1, x3],
 * and [x2, x3] in the above).
 *
 * Moreover the permutations are generated modulo rewriting, s.t. if two
 * permutations are equivalent, only one is used.
 *
 * It should be noted that the variables of a variable agnostic enumerator are
 * kept in independent "subclasses" (see TermDbSygus::getSubclassForVar).
 * Therefore when streaming concrete values, permutations and combinations are
 * generated by the product of the permutations and combinations of each class.
 */
class EnumStreamSubstitution : protected EnvObj
{
 public:
  EnumStreamSubstitution(Env& env, TermDbSygus* tds);
  ~EnumStreamSubstitution() {}
  /** initializes utility
   *
   * the combinations are generated from a initial set of variables (for now all
   * variables in given type).
   */
  void initialize(TypeNode tn);
  /** resets value for which substitutions will be generated through
   * combinations
   *
   * For each variable subclass in this utility, a subset is chosen with as
   * many variables as in the same variable subclass of value's variables.
   *
   * The combinations are performed modulo subclasses. For each subclass of the
   * given variables, a combination utility is initialized.
   *
   * For example, if the initial variable set is partioned into
   *
   * {1 -> {x1, x4}, 2 -> {x2, x3, x6}, 3 -> {x5}}
   *
   * and value's variables into
   *
   * {1 -> {x1, x4}, 2 -> {x2}, 3 -> {}}
   *
   * then the combination utilities are initialized such that for class 1 all
   * ordered subsets with two variables are chosen; for class 2 all ordered
   * subsets with one variable; and for class 3 no combination can be chosen.
   */
  void resetValue(Node value);
  /** computes next combination, if any, of value
   *
   * a "next" combination is determined by having at least one new combination
   * in one of the variable subclasses in the initial set of variables. If no
   * new combination exists, the cycle restarts with a new base value generated
   * by EnumStreamPermutation::getNext() (see above).
   *
   * This layered approach (of deriving all combinations for each permutation)
   * allows to consider only ordered combinations to generate all possible
   * variations of the base value. See the example in EnumStreamSubstitution for
   * further details.
   */
  Node getNext();

 private:
  /** sygus term database of current quantifiers engine */
  TermDbSygus* d_tds;
  /** type this utility has been initialized for */
  TypeNode d_tn;
  /** current value */
  Node d_value;
  /** maps subclass ids to d_tn's variables with that subclass id */
  std::map<unsigned, std::vector<Node>> d_var_classes;
  /** maps variables to subfield types with constructors for
   * the that variable, which are themselves associated with the respective
   * constructors */
  std::map<Node, std::map<TypeNode, Node>> d_var_tn_cons;
  /** last value generated after a combination
   *
   * If getNext() has been called, this is the return value of the most recent
   * call to getNext(). Otherwise, this value is null.
   */
  Node d_last;
  /** generated combinations */
  std::unordered_set<Node> d_comb_values;
  /** permutation utility */
  EnumStreamPermutation d_stream_permutations;
  /** Utility for stepwise generation of ordered subsets of size k from n
   * variables */
  class CombinationState
  {
   public:
    CombinationState(unsigned n,
                     unsigned k,
                     unsigned subclass_id,
                     const std::vector<Node>& vars);
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
    /** retrieve subclass id */
    const unsigned getSubclassId() const;

   private:
    /** subclass id of variables being combined */
    unsigned d_subclass_id;
    /** number of variables */
    unsigned d_n;
    /** size of subset */
    unsigned d_k;
    /** last combination state */
    std::vector<unsigned> d_last_comb;
    /** variables from which combination is extracted */
    std::vector<Node> d_vars;
  };
  /** combination state for each variable subclass */
  std::vector<CombinationState> d_comb_state_class;
  /** current class being combined */
  unsigned d_curr_ind;
};

/**
 * An enumerated value generator based on the above class. This is
 * SynthConjecture's interface to using the above utility.
 */
class EnumStreamConcrete : public EnumValGenerator
{
 public:
  EnumStreamConcrete(Env& env, TermDbSygus* tds);
  /** initialize this class with enumerator e */
  void initialize(Node e) override;
  /** get that value v was enumerated */
  void addValue(Node v) override;
  /** increment */
  bool increment() override;
  /** get the current value enumerated by this class */
  Node getCurrent() override;

 private:
  /** stream substitution utility */
  EnumStreamSubstitution d_ess;
  /** the current term generated by this class */
  Node d_currTerm;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
