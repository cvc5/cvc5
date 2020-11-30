/*********************                                                        */
/*! \file sygus_sampler.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Fabian Wolff
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief sygus_sampler
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS_SAMPLER_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS_SAMPLER_H

#include <map>
#include "theory/evaluator.h"
#include "theory/quantifiers/lazy_trie.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_enumeration.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** SygusSampler
 *
 * This class can be used to test whether two expressions are equivalent
 * by random sampling. We use this class for the following options:
 *
 * sygus-rr-synth: synthesize candidate rewrite rules by finding two terms
 * t1 and t2 do not rewrite to the same term, but are identical when considering
 * a set of sample points, and
 *
 * sygus-rr-verify: detect unsound rewrite rules by finding two terms t1 and
 * t2 that rewrite to the same term, but not identical when considering a set
 * of sample points.
 *
 * To use this class:
 * (1) Call initialize( tds, f, nsamples) where f is sygus datatype term.
 * (2) For terms n1....nm enumerated that correspond to builtin analog of sygus
 * term f, we call registerTerm( n1 )....registerTerm( nm ). It may be the case
 * that registerTerm( ni ) returns nj for some j < i. In this case, we have that
 * ni and nj are equivalent under the sample points in this class.
 *
 * For example, say the grammar for f is:
 *   A = 0 | 1 | x | y | A+A | ite( B, A, A )
 *   B = A <= A
 * If we call initialize( tds, f, 5 ), this class will generate 5 random sample
 * points for (x,y), say (0,0), (1,1), (0,1), (1,0), (2,2). The return values
 * of successive calls to registerTerm are listed below.
 *   registerTerm( 0 ) -> 0
 *   registerTerm( x ) -> x
 *   registerTerm( x+y ) -> x+y
 *   registerTerm( y+x ) -> x+y
 *   registerTerm( x+ite(x <= 1+1, 0, y ) ) -> x
 * Notice that the number of sample points can be configured for the above
 * options using sygus-samples=N.
 */
class SygusSampler : public LazyTrieEvaluator
{
 public:
  SygusSampler();
  ~SygusSampler() override {}

  /** initialize
   *
   * tn : the return type of terms we will be testing with this class,
   * vars : the variables we are testing substitutions for,
   * nsamples : number of sample points this class will test,
   * unique_type_ids : if this is set to true, then we consider each variable
   * in vars to have a unique "type id". A type id is a finer-grained notion of
   * type that is used to determine when a rewrite rule is redundant.
   */
  virtual void initialize(TypeNode tn,
                          const std::vector<Node>& vars,
                          unsigned nsamples,
                          bool unique_type_ids = false);
  /** initialize sygus
   *
   * qe : pointer to quantifiers engine,
   * f : a term of some SyGuS datatype type whose values we will be
   * testing under the free variables in the grammar of f,
   * nsamples : number of sample points this class will test,
   * useSygusType : whether we will register terms with this sampler that have
   * the same type as f. If this flag is false, then we will be registering
   * terms of the analog of the type of f, that is, the builtin type that
   * f's type encodes in the deep embedding.
   */
  virtual void initializeSygus(TermDbSygus* tds,
                               Node f,
                               unsigned nsamples,
                               bool useSygusType);
  /** register term n with this sampler database
   *
   * forceKeep is whether we wish to force that n is chosen as a representative
   * value in the trie.
   */
  virtual Node registerTerm(Node n, bool forceKeep = false);
  /** get number of sample points */
  unsigned getNumSamplePoints() const { return d_samples.size(); }
  /** get variables, adds d_vars to vars */
  void getVariables(std::vector<Node>& vars) const;
  /** get sample point
   *
   * Appends sample point #index to the vector pt, d_vars to vars.
   */
  void getSamplePoint(unsigned index,
                      std::vector<Node>& pt);
  /** Add pt to the set of sample points considered by this sampler */
  void addSamplePoint(std::vector<Node>& pt);
  /** evaluate n on sample point index */
  Node evaluate(Node n, unsigned index) override;
  /**
   * Compute the variables from the domain of d_var_index that occur in n,
   * store these in the vector fvs.
   */
  void computeFreeVariables(Node n, std::vector<Node>& fvs);
  /**
   * Returns the index of a sample point such that the evaluation of a and b
   * diverge, or -1 if no such sample point exists.
   */
  int getDiffSamplePointIndex(Node a, Node b);

  //--------------------------queries about terms
  /** is contiguous
   *
   * This returns whether n's free variables (terms occurring in the range of
   * d_type_vars) are a prefix of the list of variables in d_type_vars for each
   * type id. For instance, if d_type_vars[id] = { x, y } for some id, then
   * 0, x, x+y, y+x are contiguous but y is not. This is useful for excluding
   * terms from consideration that are alpha-equivalent to others.
   */
  bool isContiguous(Node n);
  /** is ordered
   *
   * This returns whether n's free variables are in order with respect to
   * variables in d_type_vars for each type. For instance, if
   * d_type_vars[id] = { x, y } for some id, then 0, x, x+y are ordered but
   * y and y+x are not.
   */
  bool isOrdered(Node n);
  /** is linear
   *
   * This returns whether n contains at most one occurrence of each free
   * variable. For example, x, x+y are linear, but x+x, (x-y)+y, (x+0)+(x+0) are
   * non-linear.
   */
  bool isLinear(Node n);
  /** check variables
   *
   * This returns false if !isOrdered(n) and checkOrder is true or !isLinear(n)
   * if checkLinear is true, or false otherwise.
   */
  bool checkVariables(Node n, bool checkOrder, bool checkLinear);
  /** contains free variables
   *
   * Returns true if the free variables of b are a subset of those in a, where
   * we require a strict subset if strict is true. Free variables are those that
   * occur in the range d_type_vars.
   */
  bool containsFreeVariables(Node a, Node b, bool strict = false);
  //--------------------------end queries about terms
  /** check equivalent
   *
   * Check whether bv and bvr are equivalent on all sample points, print
   * an error if not. Used with --sygus-rr-verify.
   */
  void checkEquivalent(Node bv, Node bvr);

 protected:
  /** sygus term database of d_qe */
  TermDbSygus* d_tds;
  /** term enumerator object (used for random sampling) */
  TermEnumeration d_tenum;
  /** samples */
  std::vector<std::vector<Node> > d_samples;
  /** evaluator class */
  Evaluator d_eval;
  /** data structure to check duplication of sample points */
  class PtTrie
  {
   public:
    /** add pt to this trie, returns true if pt is not a duplicate. */
    bool add(std::vector<Node>& pt);

   private:
    /** the children of this node */
    std::map<Node, PtTrie> d_children;
  };
  /** a trie for samples */
  PtTrie d_samples_trie;
  /** the sygus type for this sampler (if applicable). */
  TypeNode d_ftn;
  /** whether we are registering terms of sygus types with this sampler */
  bool d_use_sygus_type;
  /**
   * For each (sygus) type, a map from builtin terms to the sygus term they
   * correspond to.
   */
  std::map<TypeNode, std::map<Node, Node> > d_builtin_to_sygus;
  /** all variables we are sampling values for */
  std::vector<Node> d_vars;
  /** type variables
   *
   * We group variables according to "type ids". Two variables have the same
   * type id if they have indistinguishable status according to this sampler.
   * This is a finer-grained grouping than types. For example, two variables
   * of the same type may have different type ids if they occur as constructors
   * of a different set of sygus types in the grammar we are considering.
   * For instance, we assign x and y different type ids in this grammar:
   *   A -> B + C
   *   B -> x | 0 | 1
   *   C -> y
   * Type ids are computed for each variable in d_vars during initialize(...).
   *
   * For each type id, a list of variables in the grammar we are considering,
   * for that type. These typically correspond to the arguments of the
   * function-to-synthesize whose grammar we are considering.
   */
  std::map<unsigned, std::vector<Node> > d_type_vars;
  /**
   * A map all variables in the grammar we are considering to their index in
   * d_type_vars.
   */
  std::map<Node, unsigned> d_var_index;
  /**  Map from variables to the id (the domain of d_type_vars). */
  std::map<Node, unsigned> d_type_ids;
  /** constants
   *
   * For each type, a list of constants in the grammar we are considering, for
   * that type.
   */
  std::map<TypeNode, std::vector<Node> > d_type_consts;
  /** a lazy trie for each type
   *
   * This stores the evaluation of all terms registered to this class.
   *
   * Notice if we are registering sygus terms with this class, then terms
   * are grouped into this trie according to their sygus type, and not their
   * builtin type. For example, for grammar:
   *   A -> x | B+1
   *   B -> x | 0 | 1 | B+B
   * If we register C^B_+( C^B_x(), C^B_0() ) and C^A_x() with this class,
   * then x+0 is registered to d_trie[B] and x is registered to d_trie[A],
   * and no rewrite rule is reported. The reason for this is that otherwise
   * we would end up reporting many useless rewrites since the same builtin
   * term can be generated by multiple sygus types (e.g. C^B_x() and C^A_x()).
   */
  std::map<TypeNode, LazyTrie> d_trie;
  /** is this sampler valid?
   *
   * A sampler can be invalid if sample points cannot be generated for a type
   * of an argument to function f.
   */
  bool d_is_valid;
  /** initialize samples
   *
   * Adds nsamples sample points to d_samples.
   */
  void initializeSamples(unsigned nsamples);
  /** get random value for a type
   *
   * Returns a random value for the given type based on the random number
   * generator. Currently, supported types:
   *
   * Bool, Bitvector : returns a random value in the range of that type.
   * Int, String : returns a random string of values in (base 10) of random
   * length, currently by a repeated coin flip.
   * Real : returns the division of two random integers, where the denominator
   * is omitted if it is zero.
   */
  Node getRandomValue(TypeNode tn);
  /** get sygus random value
   *
   * Returns a random value based on the sygus type tn. The return value is
   * a constant in the analog type of tn. This function chooses either to
   * return a random value, or otherwise will construct a constant based on
   * a random constructor of tn whose builtin operator is not a variable.
   *
   * rchance: the chance that the call to this function will be forbidden
   * from making recursive calls and instead must return a value based on
   * a nullary constructor of tn or based on getRandomValue above.
   * rinc: the percentage to increment rchance on recursive calls.
   *
   * For example, consider the grammar:
   *   A -> x | y | 0 | 1 | +( A, A ) | ite( B, A, A )
   *   B -> A = A
   * If we call this function on A and rchance is 0.0, there are five evenly
   * chosen possibilities, either we return a random value via getRandomValue
   * above, or we choose one of the four non-variable constructors of A.
   * Say we choose ite, then we recursively call this function for
   * B, A, and A, which return constants c1, c2, and c3. Then, this function
   * returns the rewritten form of ite( c1, c2, c3 ).
   * If on the other hand, rchance was 0.5 and rand() < 0.5. Then, we force
   * this call to terminate by either selecting a random value via
   * getRandomValue, 0 or 1.
   */
  Node getSygusRandomValue(TypeNode tn,
                           double rchance,
                           double rinc,
                           unsigned depth = 0);
  /** map from sygus types to non-variable constructors */
  std::map<TypeNode, std::vector<unsigned> > d_rvalue_cindices;
  /** map from sygus types to non-variable nullary constructors */
  std::map<TypeNode, std::vector<unsigned> > d_rvalue_null_cindices;
  /** the random string alphabet */
  std::vector<unsigned> d_rstring_alphabet;
  /** map from variables to sygus types that include them */
  std::map<Node, std::vector<TypeNode> > d_var_sygus_types;
  /** map from constants to sygus types that include them */
  std::map<Node, std::vector<TypeNode> > d_const_sygus_types;
  /** register sygus type, initializes the above two data structures */
  void registerSygusType(TypeNode tn);
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__SYGUS_SAMPLER_H */
