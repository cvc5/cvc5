/*********************                                                        */
/*! \file datatypes_sygus.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Paul Meng, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sygus utilities for theory of datatypes
 **
 ** Theory of datatypes.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__DATATYPES__DATATYPES_SYGUS_NEW_H
#define __CVC4__THEORY__DATATYPES__DATATYPES_SYGUS_NEW_H

#include <iostream>
#include <map>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "context/cdo.h"
#include "context/context.h"
#include "expr/datatype.h"
#include "expr/node.h"
#include "theory/quantifiers/sygus/ce_guided_conjecture.h"
#include "theory/quantifiers/sygus/sygus_explain.h"
#include "theory/quantifiers/sygus_sampler.h"
#include "theory/quantifiers/term_database.h"

namespace CVC4 {
namespace theory {
namespace datatypes {

class TheoryDatatypes;

class SygusSymBreakNew
{
  typedef context::CDHashMap< Node, int, NodeHashFunction > IntMap;
  typedef context::CDHashMap< Node, Node, NodeHashFunction > NodeMap;
  typedef context::CDHashMap< Node, bool, NodeHashFunction > BoolMap;
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

 public:
  SygusSymBreakNew(TheoryDatatypes* td,
                   quantifiers::TermDbSygus* tds,
                   context::Context* c);
  ~SygusSymBreakNew();
  /** add tester */
  void assertTester(int tindex, TNode n, Node exp, std::vector<Node>& lemmas);
  void assertFact(Node n, bool polarity, std::vector<Node>& lemmas);
  void preRegisterTerm(TNode n, std::vector<Node>& lemmas);
  void check(std::vector<Node>& lemmas);
  Node getNextDecisionRequest(unsigned& priority, std::vector<Node>& lemmas);

 private:
  /** Pointer to the datatype theory that owns this class. */
  TheoryDatatypes* d_td;
  /** Pointer to the sygus term database */
  quantifiers::TermDbSygus* d_tds;
  IntMap d_testers;
  IntMap d_is_const;
  NodeMap d_testers_exp;
  NodeSet d_active_terms;
  IntMap d_currTermSize;
  Node d_zero;
  /**
   * Map from terms (selector chains) to their anchors. The anchor of a
   * selector chain S1( ... Sn( x ) ... ) is x.
   */
  std::unordered_map<Node, Node, NodeHashFunction> d_term_to_anchor;
  /**
   * Map from anchors to the conjecture they are associated with.
   */
  std::map<Node, quantifiers::CegConjecture*> d_anchor_to_conj;
  /**
   * Map from terms (selector chains) to their depth. The depth of a selector
   * chain S1( ... Sn( x ) ... ) is:
   *   weight( S1 ) + ... + weight( Sn ),
   * where weight is the selector weight of Si
   * (see SygusTermDatabase::getSelectorWeight).
   */
  std::unordered_map<Node, unsigned, NodeHashFunction> d_term_to_depth;
  /**
   * Map from terms (selector chains) to whether they are the topmost term
   * of their type. For example, if:
   *   S1 : T1 -> T2
   *   S2 : T2 -> T2
   *   S3 : T2 -> T1
   *   S4 : T1 -> T3
   * Then, x, S1( x ), and S4( S3( S2( S1( x ) ) ) ) are top-level terms,
   * whereas S2( S1( x ) ) and S3( S2( S1( x ) ) ) are not.
   *
   */
  std::unordered_map<Node, bool, NodeHashFunction> d_is_top_level;
  /**
   * Returns true if the selector chain n is top-level based on the above
   * definition, when tn is the type of n.
   */
  bool computeTopLevel( TypeNode tn, Node n );
private:
 /** This caches all information regarding symmetry breaking for an anchor. */
 class SearchCache
 {
  public:
    SearchCache(){}
    /**
     * A cache of all search terms for (types, sizes). See registerSearchTerm
     * for definition of search terms.
     */
    std::map< TypeNode, std::map< unsigned, std::vector< Node > > > d_search_terms;
    /** A cache of all symmetry breaking lemma templates for (types, sizes). */
    std::map< TypeNode, std::map< unsigned, std::vector< Node > > > d_sb_lemmas;
    /** search value
     *
     * For each sygus type, a map from a builtin term to a sygus term for that
     * type that we encountered during the search whose analog rewrites to that
     * term. The range of this map can be updated if we later encounter a sygus
     * term that also rewrites to the builtin value but has a smaller term size.
     */
    std::map<TypeNode, std::unordered_map<Node, Node, NodeHashFunction>>
        d_search_val;
    /** the size of terms in the range of d_search val. */
    std::map<TypeNode, std::unordered_map<Node, unsigned, NodeHashFunction>>
        d_search_val_sz;
    /** For each term, whether this cache has processed that term */
    std::unordered_set<Node, NodeHashFunction> d_search_val_proc;
  };
  /** An instance of the above cache, for each anchor */
  std::map< Node, SearchCache > d_cache;
  /** a sygus sampler object for each (anchor, sygus type) pair
   *
   * This is used for the sygusRewVerify() option to verify the correctness of
   * the rewriter.
   */
  std::map<Node, std::map<TypeNode, quantifiers::SygusSampler>> d_sampler;
  /** Assert tester internal
   *
   * This function is called when the tester with index tindex is asserted for
   * n, exp is the tester predicate. For example, for grammar:
   *   A -> A+A | x | 1 | 0
   * when is_+( d ) is asserted,
   * assertTesterInternal(0, s( d ), is_+( s( d ) ),...) is called. This
   * function may add lemmas to lemmas, which are sent out on the output
   * channel of datatypes by the caller.
   *
   * These lemmas are of various forms, including:
   * (1) dynamic symmetry breaking clauses for subterms of n (those added to
   * lemmas on calls to addSymBreakLemmasFor, see function below),
   * (2) static symmetry breaking clauses for subterms of n (those added to
   * lemmas on getSimpleSymBreakPred, see function below),
   * (3) conjecture-specific symmetry breaking lemmas, see
   * CegConjecture::getSymmetryBreakingPredicate,
   * (4) fairness conflicts if sygusFair() is SYGUS_FAIR_DIRECT, e.g.:
   *    size( d ) <= 1 V ~is-C1( d ) V ~is-C2( d.1 )
   * where C1 and C2 are non-nullary constructors.
   */
  void assertTesterInternal( int tindex, TNode n, Node exp, std::vector< Node >& lemmas );
  /**
   * This function is called when term n is registered to the theory of
   * datatypes. It makes the appropriate call to registerSearchTerm below,
   * if applicable.
   */
  void registerTerm(Node n, std::vector<Node>& lemmas);

  //------------------------dynamic symmetry breaking
  /** Register search term
   *
   * This function is called when selector chain n of the form
   * S_1( ... S_m( x ) ... ) is registered to the theory of datatypes, where
   * tn is the type of n, d indicates the depth of n (the sum of weights of the
   * selectors S_1...S_m), and topLevel is whether n is a top-level term
   * (see d_is_top_level). We refer to n as a "search term".
   *
   * The purpose of this function is to notify this class that symmetry breaking
   * lemmas should be instantiated for n. Any symmetry breaking lemmas that
   * are active for n (see description of addSymBreakLemmasFor) are added to
   * lemmas in this call.
   */
  void registerSearchTerm( TypeNode tn, unsigned d, Node n, bool topLevel, std::vector< Node >& lemmas );
  /** Register search value
   *
   * This function is called when a selector chain n has been assigned a model
   * value nv. This function calls itself recursively so that extensions of the
   * selector chain n are registered with all the subterms of nv. For example,
   * if we call this function with:
   *   n = x, nv = +( 1(), x() )
   * we make recursive calls with:
   *   n = x.1, nv = 1() and n = x.2, nv = x()
   *
   * a : the anchor of n,
   * d : the depth of n.
   *
   * This function determines if the value nv is equivalent via rewriting to
   * any previously registered search values for anchor a. If so, we construct
   * a symmetry breaking lemma template and register it in d_cache[a]. For
   * example, for grammar:
   *   A -> A+A | x | 1 | 0
   * Registering search value d -> x followed by d -> +( x, 0 ) results in the
   * construction of the symmetry breaking lemma template:
   *   ~is_+( z ) V ~is_x( z.1 ) V ~is_0( z.2 )
   * which is stored in d_cache[a].d_sb_lemmas. This lemma is instantiated with
   * z -> t for all terms t of appropriate depth, including d.
   * This function strengthens blocking clauses using generalization techniques
   * described in Reynolds et al SYNT 2017.
   */
  bool registerSearchValue( Node a, Node n, Node nv, unsigned d, std::vector< Node >& lemmas );
  /** Register symmetry breaking lemma
   *
   * This function adds the symmetry breaking lemma template lem for terms of
   * type tn with anchor a. This is added to d_cache[a].d_sb_lemmas. Notice that
   * we use lem as a template with free variable x, e.g. our template is:
   *   (lambda ((x tn)) lem)
   * where x = getFreeVar( tn ). For all search terms t of the appropriate
   * depth,
   * we add the lemma lem{ x -> t } to lemmas.
   *
   * The argument sz indicates the size of terms that the lemma applies to, e.g.
   *   ~is_+( z ) has size 1
   *   ~is_+( z ) V ~is_x( z.1 ) V ~is_0( z.2 ) has size 1
   *   ~is_+( z ) V ~is_+( z.1 ) has size 2
   * This is equivalent to sum of weights of constructors corresponding to each
   * tester, e.g. above + has weight 1, and x and 0 have weight 0.
   */
  void registerSymBreakLemma(
      TypeNode tn, Node lem, unsigned sz, Node a, std::vector<Node>& lemmas);
  /** Register symmetry breaking lemma for value
   *
   * This function adds a symmetry breaking lemma template for selector chains
   * with anchor a, that effectively states that val should never be a subterm
   * of any value for a.
   *
   * et : an "invariance test" (see sygus/sygus_invariance.h) which states a
   * criterion that val meets, which is the reason for its exclusion. This is
   * used for generalizing the symmetry breaking lemma template.
   * valr : if non-null, this states a value that should *not* be excluded by
   * the symmetry breaking lemma template, which is a restriction to the above
   * generalization.
   *
   * This function may add instances of the symmetry breaking template for
   * existing search terms, which are added to lemmas.
   */
  void registerSymBreakLemmaForValue(Node a,
                                     Node val,
                                     quantifiers::SygusInvarianceTest& et,
                                     Node valr,
                                     std::vector<Node>& lemmas);
  /** Add symmetry breaking lemmas for term
   *
   * Adds all active symmetry breaking lemmas for selector chain t to lemmas. A
   * symmetry breaking lemma L is active for t based on three factors:
   * (1) the current search size sz(a) for its anchor a,
   * (2) the depth d of term t (see d_term_to_depth),
   * (3) the size sz(L) of the symmetry breaking lemma L.
   * In particular, L is active if sz(L) <= sz(a) - d. In other words, a
   * symmetry breaking lemma is active if it is intended to block terms of
   * size sz(L), and the maximum size that t can take in the current search,
   * sz(a)-d, is greater than or equal to this value.
   *
   * tn : the type of term t,
   * a : the anchor of term t,
   * d : the depth of term t.
   */
  void addSymBreakLemmasFor(
      TypeNode tn, Node t, unsigned d, Node a, std::vector<Node>& lemmas);
  /** calls the above function where a is the anchor t */
  void addSymBreakLemmasFor( TypeNode tn, Node t, unsigned d, std::vector< Node >& lemmas );
  /** add symmetry breaking lemma
   *
   * This adds the lemma R => lem{ x -> n } to lemmas, where R is a "relevancy
   * condition" that states which contexts n is relevant in (see
   * getRelevancyCondition).
   */
  void addSymBreakLemma(Node lem, TNode x, TNode n, std::vector<Node>& lemmas);
  //------------------------end dynamic symmetry breaking

  /** Get relevancy condition
   *
   * This returns a predicate that holds in the contexts in which the selector
   * chain n is specified. For example, the relevancy condition for
   * sel_{C2,1}( sel_{C1,1}( d ) ) is is-C1( d ) ^ is-C2( sel_{C1,1}( d ) ).
   * If shared selectors are enabled, this is a conjunction of disjunctions,
   * since shared selectors may apply to multiple constructors.
   */
  Node getRelevancyCondition( Node n );
  /** Cache of the above function */
  std::map<Node, Node> d_rlv_cond;

  //------------------------static symmetry breaking
  /** Get simple symmetry breakind predicate
   *
   * This function returns the "static" symmetry breaking lemma template for
   * terms with type tn and constructor index tindex, for the given depth. This
   * includes inferences about size with depth=0. Given grammar:
   *   A -> ite( B, A, A ) | A+A | x | 1 | 0
   *   B -> A = A
   * Examples of static symmetry breaking lemma templates are:
   *   for +, depth 0: size(z)=size(z.1)+size(z.2)+1
   *   for +, depth 1: ~is-0( z.1 ) ^ ~is-0( z.2 ) ^ F
   *     where F ensures the constructor of z.1 is less than that of z.2 based
   *     on some ordering.
   *   for ite, depth 1: z.2 != z.3
   * These templates can be thought of as "hard-coded" cases of dynamic symmetry
   * breaking lemma templates. Notice that the above lemma templates are in
   * terms of getFreeVar( tn ), hence only one is created per
   * (constructor, depth). A static symmetry break lemma template F[z] for
   * constructor C are included in lemmas of the form:
   *   is-C( t ) => F[t]
   * where t is a search term, see registerSearchTerm for definition of search
   * term.
   */
  Node getSimpleSymBreakPred( TypeNode tn, int tindex, unsigned depth );
  /** Cache of the above function */
  std::map<TypeNode, std::map<int, std::map<unsigned, Node>>> d_simple_sb_pred;
  /**
   * For each search term, this stores the maximum depth for which we have added
   * a static symmetry breaking lemma.
   *
   * This should be user context-dependent if sygus is updated to work in
   * incremental mode.
   */
  std::unordered_map<Node, unsigned, NodeHashFunction> d_simple_proc;
  //------------------------end static symmetry breaking

  /** Get the canonical free variable for type tn */
  TNode getFreeVar( TypeNode tn );
  Node getTermOrderPredicate( Node n1, Node n2 );
private:
 /**
  * Map from registered variables to whether they are a sygus enumerator.
  *
  * This should be user context-dependent if sygus is updated to work in
  * incremental mode.
  */
 std::map<Node, bool> d_register_st;
 void registerSizeTerm(Node e, std::vector<Node>& lemmas);
 class SearchSizeInfo
 {
  public:
    SearchSizeInfo( Node t, context::Context* c ) : d_this( t ), d_curr_search_size(0), d_curr_lit( c, 0 ) {}
    Node d_this;
    std::map< unsigned, Node > d_search_size_exp;
    std::map< unsigned, bool > d_search_size;
    unsigned d_curr_search_size;
    Node d_sygus_measure_term;
    Node d_sygus_measure_term_active;
    std::vector< Node > d_anchors;
    Node getOrMkSygusMeasureTerm( std::vector< Node >& lemmas );
    Node getOrMkSygusActiveMeasureTerm( std::vector< Node >& lemmas );
  public:
    /** current cardinality */
    context::CDO< unsigned > d_curr_lit;
    std::map< unsigned, Node > d_lits;
    Node getFairnessLiteral( unsigned s, TheoryDatatypes * d, std::vector< Node >& lemmas );
    Node getCurrentFairnessLiteral( TheoryDatatypes * d, std::vector< Node >& lemmas ) { 
      return getFairnessLiteral( d_curr_lit.get(), d, lemmas ); 
    }
    /** increment current term size */
    void incrementCurrentLiteral() { d_curr_lit.set( d_curr_lit.get() + 1 ); }
  };
  std::map< Node, SearchSizeInfo * > d_szinfo;
  std::map< Node, Node > d_anchor_to_measure_term;
  std::map< Node, Node > d_anchor_to_active_guard;
  Node d_generic_measure_term;
  void incrementCurrentSearchSize( Node m, std::vector< Node >& lemmas );
  void notifySearchSize( Node m, unsigned s, Node exp, std::vector< Node >& lemmas );
  void registerMeasureTerm( Node m );
  unsigned getSearchSizeFor( Node n );
  unsigned getSearchSizeForAnchor( Node n );
  unsigned getSearchSizeForMeasureTerm(Node m);

 private:
  unsigned processSelectorChain( Node n, std::map< TypeNode, Node >& top_level, 
                                 std::map< Node, unsigned >& tdepth, std::vector< Node >& lemmas );
  bool debugTesters( Node n, Node vn, int ind, std::vector< Node >& lemmas );
  Node getCurrentTemplate( Node n, std::map< TypeNode, int >& var_count );
  int getGuardStatus( Node g );
private:
  void assertIsConst( Node n, bool polarity, std::vector< Node >& lemmas );
};

}
}
}

#endif

