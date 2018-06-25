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
#include "theory/quantifiers/lazy_trie.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"

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
   * f : a term of some SyGuS datatype type whose values we will be
   * testing under the free variables in the grammar of f,
   * nsamples : number of sample points this class will test,
   * useSygusType : whether we will register terms with this sampler that have
   * the same type as f. If this flag is false, then we will be registering
   * terms of the analog of the type of f, that is, the builtin type that
   * f's type encodes in the deep embedding.
   */
  void initializeSygus(TermDbSygus* tds,
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
                      std::vector<Node>& vars,
                      std::vector<Node>& pt);
  /** Add pt to the set of sample points considered by this sampler */
  void addSamplePoint(std::vector<Node>& pt);
  /** evaluate n on sample point index */
  Node evaluate(Node n, unsigned index) override;
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
   * Returns true if the free variables of b are a subset of those in a, where
   * we require a strict subset if strict is true. Free variables are those that
   * occur in the range d_type_vars.
   */
  bool containsFreeVariables(Node a, Node b, bool strict = false);

 protected:
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
  /** whether we are registering terms of type d_ftn */
  bool d_use_sygus_type;
  /** map from builtin terms to the sygus term they correspond to */
  std::map<Node, Node> d_builtin_to_sygus;
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
  /** the random string alphabet */
  std::vector<unsigned> d_rstring_alphabet;
  /** map from variables to sygus types that include them */
  std::map<Node, std::vector<TypeNode> > d_var_sygus_types;
  /** map from constants to sygus types that include them */
  std::map<Node, std::vector<TypeNode> > d_const_sygus_types;
  /** register sygus type, intializes the above two data structures */
  void registerSygusType(TypeNode tn);
};

/** A virtual class for notifications regarding matches. */
class NotifyMatch
{
 public:
  virtual ~NotifyMatch() {}

  /**
   * A notification that s is equal to n * { vars -> subs }. This function
   * should return false if we do not wish to be notified of further matches.
   */
  virtual bool notify(Node s,
                      Node n,
                      std::vector<Node>& vars,
                      std::vector<Node>& subs) = 0;
};

/**
 * A trie (discrimination tree) storing a set of terms S, that can be used to
 * query, for a given term t, all terms from S that are matchable with t.
 */
class MatchTrie
{
 public:
  /** Get matches
   *
   * This calls ntm->notify( n, s, vars, subs ) for each term s stored in this
   * trie that is matchable with n where s = n * { vars -> subs } for some
   * vars, subs. This function returns false if one of these calls to notify
   * returns false.
   */
  bool getMatches(Node n, NotifyMatch* ntm);
  /** Adds node n to this trie */
  void addTerm(Node n);
  /** Clear this trie */
  void clear();

 private:
  /**
   * The children of this node in the trie. Terms t are indexed by a
   * depth-first (right to left) traversal on its subterms, where the
   * top-symbol of t is indexed by:
   * - (operator, #children) if t has an operator, or
   * - (t, 0) if t does not have an operator.
   */
  std::map<Node, std::map<unsigned, MatchTrie> > d_children;
  /** The set of variables in the domain of d_children */
  std::vector<Node> d_vars;
  /** The data of this node in the trie */
  Node d_data;
};

/** Version of the above class with some additional features */
class SygusSamplerExt : public SygusSampler
{
 public:
  SygusSamplerExt();
  /** initialize extended */
  void initializeSygusExt(QuantifiersEngine* qe,
                          Node f,
                          unsigned nsamples,
                          bool useSygusType);
  /** register term n with this sampler database
   *
   *  For each call to registerTerm( t, ... ) that returns s, we say that
   * (t,s) and (s,t) are "relevant pairs".
   *
   * This returns either null, or a term ret with the same guarantees as
   * SygusSampler::registerTerm with the additional guarantee
   * that for all previous relevant pairs ( n', nret' ),
   * we have that n = ret is not an instance of n' = ret'
   * modulo symmetry of equality, nor is n = ret derivable from the set of
   * all previous relevant pairs. The latter is determined by the d_drewrite
   * utility. For example:
   * [1]  ( t+0, t ) and ( x+0, x )
   * will not both be relevant pairs of this function since t+0=t is
   * an instance of x+0=x.
   * [2]  ( s, t ) and ( s+0, t+0 )
   * will not both be relevant pairs of this function since s+0=t+0 is
   * derivable from s=t.
   * These two criteria may be combined, for example:
   * [3] ( t+0, s ) is not a relevant pair if both ( x+0, x+s ) and ( t+s, s )
   * are relevant pairs, since t+0 is an instance of x+0 where
   * { x |-> t }, and x+s { x |-> t } = s is derivable, via the third pair
   * above (t+s = s).
   *
   * If this function returns null, then n is equivalent to a previously
   * registered term ret, and the equality ( n, ret ) is either an instance
   * of a previous relevant pair ( n', ret' ), or n = ret is derivable
   * from the set of all previous relevant pairs based on the
   * d_drewrite utility, or is an instance of a previous pair
   */
  Node registerTerm(Node n, bool forceKeep = false) override;

  /** register relevant pair
   *
   * This should be called after registerTerm( n ) returns eq_n.
   * This registers ( n, eq_n ) as a relevant pair with this class.
   */
  void registerRelevantPair(Node n, Node eq_n);

 private:
  /** dynamic rewriter class */
  std::unique_ptr<DynamicRewriter> d_drewrite;

  //----------------------------match filtering
  /**
   * Stores all relevant pairs returned by this sampler (see registerTerm). In
   * detail, if (t,s) is a relevant pair, then t in d_pairs[s].
   */
  std::map<Node, std::unordered_set<Node, NodeHashFunction> > d_pairs;
  /** Match trie storing all terms in the domain of d_pairs. */
  MatchTrie d_match_trie;
  /** Notify class */
  class SygusSamplerExtNotifyMatch : public NotifyMatch
  {
    SygusSamplerExt& d_sse;

   public:
    SygusSamplerExtNotifyMatch(SygusSamplerExt& sse) : d_sse(sse) {}
    /** notify match */
    bool notify(Node n,
                Node s,
                std::vector<Node>& vars,
                std::vector<Node>& subs) override
    {
      return d_sse.notify(n, s, vars, subs);
    }
  };
  /** Notify object used for reporting matches from d_match_trie */
  SygusSamplerExtNotifyMatch d_ssenm;
  /**
   * Stores the current right hand side of a pair we are considering.
   *
   * In more detail, in registerTerm, we are interested in whether a pair (s,t)
   * is a relevant pair. We do this by:
   * (1) Setting the node d_curr_pair_rhs to t,
   * (2) Using d_match_trie, compute all terms s1...sn that match s.
   * For each si, where s = si * sigma for some substitution sigma, we check
   * whether t = ti * sigma for some previously relevant pair (si,ti), in
   * which case (s,t) is an instance of (si,ti).
   */
  Node d_curr_pair_rhs;
  /**
   * Called by the above class during d_match_trie.getMatches( s ), when we
   * find that si = s * sigma, where si is a term that is stored in
   * d_match_trie.
   *
   * This function returns false if ( s, d_curr_pair_rhs ) is an instance of
   * previously relevant pair.
   */
  bool notify(Node s, Node n, std::vector<Node>& vars, std::vector<Node>& subs);
  //----------------------------end match filtering
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__SYGUS_SAMPLER_H */
