/*********************                                                        */
/*! \file sygus_sampler.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief sygus_sampler
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__SYGUS_SAMPLER_H
#define __CVC4__THEORY__QUANTIFIERS__SYGUS_SAMPLER_H

#include <map>
#include "theory/quantifiers/dynamic_rewrite.h"
#include "theory/quantifiers/term_database_sygus.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** abstract evaluator class
 *
 * This class is used for the LazyTrie data structure below.
 */
class LazyTrieEvaluator
{
 public:
  virtual ~LazyTrieEvaluator() {}
  virtual Node evaluate(Node n, unsigned index) = 0;
};

/** LazyTrie
 *
 * This is a trie where terms are added in a lazy fashion. This data structure
 * is useful, for instance, when we are only interested in when two terms
 * map to the same node in the trie but we need not care about computing
 * exactly where they are.
 *
 * In other words, when a term n is added to this trie, we do not insist
 * that n is placed at the maximal depth of the trie. Instead, we place n at a
 * minimal depth node that has no children. In this case we say n is partially
 * evaluated in this trie.
 *
 * This class relies on an abstract evaluator interface above, which evaluates
 * nodes for indices.
 *
 * For example, say we have terms a, b, c and an evaluator ev where:
 *   ev->evaluate( a, 0,1,2 ) = 0, 5, 6
 *   ev->evaluate( b, 0,1,2 ) = 1, 3, 0
 *   ev->evaluate( c, 0,1,2 ) = 1, 3, 2
 * After adding a to the trie, we get:
 *   root: a
 * After adding b to the resulting trie, we get:
 *   root: null
 *     d_children[0]: a
 *     d_children[1]: b
 * After adding c to the resulting trie, we get:
 *   root: null
 *     d_children[0]: a
 *     d_children[1]: null
 *       d_children[3]: null
 *         d_children[0] : b
 *         d_children[2] : c
 * Notice that we need not call ev->evalute( a, 1 ) and ev->evalute( a, 2 ).
 */
class LazyTrie
{
 public:
  LazyTrie() {}
  ~LazyTrie() {}
  /** the data at this node, which may be partially evaluated */
  Node d_lazy_child;
  /** the children of this node */
  std::map<Node, LazyTrie> d_children;
  /** clear the trie */
  void clear() { d_children.clear(); }
  /** add n to the trie
   *
   * This function returns a node that is mapped to the same node in the trie
   * if one exists, or n otherwise.
   *
   * ev is an evaluator which determines where n is placed in the trie
   * index is the depth of this node
   * ntotal is the maximal depth of the trie
   * forceKeep is whether we wish to force that n is chosen as a representative
   */
  Node add(Node n,
           LazyTrieEvaluator* ev,
           unsigned index,
           unsigned ntotal,
           bool forceKeep);
};

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
 * If we call intialize( tds, f, 5 ), this class will generate 5 random sample
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
   * tn : the return type of terms we will be testing with this class
   * vars : the variables we are testing substitutions for
   * nsamples : number of sample points this class will test.
   */
  void initialize(TypeNode tn, std::vector<Node>& vars, unsigned nsamples);
  /** initialize sygus
   *
   * tds : pointer to sygus database,
   * f : a term of some SyGuS datatype type whose (builtin) values we will be
   * testing under the free variables in the grammar of f,
   * nsamples : number of sample points this class will test.
   */
  void initializeSygus(TermDbSygus* tds, Node f, unsigned nsamples);
  /** register term n with this sampler database
   *
   * forceKeep is whether we wish to force that n is chosen as a representative
   * value in the trie.
   */
  virtual Node registerTerm(Node n, bool forceKeep = false);
  /** get number of sample points */
  unsigned getNumSamplePoints() const { return d_samples.size(); }
  /** get sample point
   *
   * Appends sample point #index to the vector pt, d_vars to vars.
   */
  void getSamplePoint(unsigned index,
                      std::vector<Node>& vars,
                      std::vector<Node>& pt);
  /** evaluate n on sample point index */
  Node evaluate(Node n, unsigned index);
  /**
   * Returns the index of a sample point such that the evaluation of a and b
   * diverge, or -1 if no such sample point exists.
   */
  int getDiffSamplePointIndex(Node a, Node b);

 protected:
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
  /** contains free variables
   *
   * Returns true if all free variables of a are contained in b. Free variables
   * are those that occur in the range d_type_vars.
   */
  bool containsFreeVariables(Node a, Node b);
 private:
  /** sygus term database of d_qe */
  TermDbSygus* d_tds;
  /** samples */
  std::vector<std::vector<Node> > d_samples;
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
  /** type of nodes we will be registering with this class */
  TypeNode d_tn;
  /** the sygus type for this sampler (if applicable). */
  TypeNode d_ftn;
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
  /** the lazy trie */
  LazyTrie d_trie;
  /** is this sampler valid?
   *
   * A sampler can be invalid if sample points cannot be generated for a type
   * of an argument to function f.
   */
  bool d_is_valid;
  /**
   * Compute the variables from the domain of d_var_index that occur in n,
   * store these in the vector fvs.
   */
  void computeFreeVariables(Node n, std::vector<Node>& fvs);
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
  /** map from variables to sygus types that include them */
  std::map<Node, std::vector<TypeNode> > d_var_sygus_types;
  /** register sygus type, intializes the above two data structures */
  void registerSygusType(TypeNode tn);
};

/** Version of the above class with some additional features */
class SygusSamplerExt : public SygusSampler
{
 public:
  /** initialize extended */
  void initializeSygusExt(QuantifiersEngine* qe, Node f, unsigned nsamples);
  /** register term n with this sampler database
   *
   * This returns either null, or a term ret with the same guarantees as
   * SygusSampler::registerTerm with the additional guarantee
   * that for all ret' returned by a previous call to registerTerm( n' ),
   * we have that n = ret is not alpha-equivalent to n' = ret'
   * modulo symmetry of equality, nor is n = ret derivable from the set of
   * all previous input/output pairs based on the d_drewrite utility.
   * For example,
   *   (t+0), t and (s+0), s
   * will not both be input/output pairs of this function since t+0=t is
   * alpha-equivalent to s+0=s.
   *   s, t and s+0, t+0
   * will not both be input/output pairs of this function since s+0=t+0 is
   * derivable from s=t.
   *
   * If this function returns null, then n is equivalent to a previously
   * registered term ret, and the equality n = ret is either alpha-equivalent
   * to a previous input/output pair n' = ret', or n = ret is derivable
   * from the set of all previous input/output pairs based on the
   * d_drewrite utility.
   */
  virtual Node registerTerm(Node n, bool forceKeep = false) override;

 private:
  /** dynamic rewriter class */
  std::unique_ptr<DynamicRewriter> d_drewrite;
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__SYGUS_SAMPLER_H */
