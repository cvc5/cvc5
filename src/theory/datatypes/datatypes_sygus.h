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
#include "theory/quantifiers/ce_guided_conjecture.h"
#include "theory/quantifiers/sygus_sampler.h"
#include "theory/quantifiers/term_database.h"

namespace CVC4 {
namespace theory {
namespace datatypes {

class TheoryDatatypes;

class SygusSplitNew
{
private:
  quantifiers::TermDbSygus * d_tds;
  std::map< Node, std::vector< Node > > d_splits;
public:
  SygusSplitNew( quantifiers::TermDbSygus * tds ) : d_tds( tds ){}
  virtual ~SygusSplitNew(){}
  /** get sygus splits */
  void getSygusSplits( Node n, const Datatype& dt, std::vector< Node >& splits, std::vector< Node >& lemmas );
  static Node getSygusSplit( quantifiers::TermDbSygus * tds, Node n, const Datatype& dt );
};

class SygusSymBreakNew
{
private:
  TheoryDatatypes * d_td;
  quantifiers::TermDbSygus * d_tds;
  typedef context::CDHashMap< Node, int, NodeHashFunction > IntMap;
  typedef context::CDHashMap< Node, Node, NodeHashFunction > NodeMap;
  typedef context::CDHashMap< Node, bool, NodeHashFunction > BoolMap;
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;
  IntMap d_testers;
  IntMap d_is_const;
  NodeMap d_testers_exp;
  NodeSet d_active_terms;
  IntMap d_currTermSize;
  Node d_zero;
private:
  std::map< Node, Node > d_term_to_anchor;
  std::map<Node, quantifiers::CegConjecture*> d_term_to_anchor_conj;
  std::map< Node, unsigned > d_term_to_depth;
  std::map< Node, bool > d_is_top_level;
  void registerTerm( Node n, std::vector< Node >& lemmas );
  bool computeTopLevel( TypeNode tn, Node n );
private:
  //list of all terms encountered in search at depth
  class SearchCache {
  public:
    SearchCache(){}
    std::map< TypeNode, std::map< unsigned, std::vector< Node > > > d_search_terms;
    std::map< TypeNode, std::map< unsigned, std::vector< Node > > > d_sb_lemmas;
    /** search value
     *
     * For each sygus type, a map from a builtin term to a sygus term for that
     * type that we encountered during the search whose analog rewrites to that
     * term. The range of this map can be updated if we later encounter a sygus
     * term that also rewrites to the builtin value but has a smaller term size.
     */
    std::map< TypeNode, std::map< Node, Node > > d_search_val;
    /** the size of terms in the range of d_search val. */
    std::map< TypeNode, std::map< Node, unsigned > > d_search_val_sz;
    /** search value sample
     *
     * This is used for the sygusRewVerify() option. For each sygus term we
     * register in this cache, this stores the value returned by calling
     * SygusSample::registerTerm(...) on its analog.
     */
    std::map<Node, Node> d_search_val_sample;
    /** For each term, whether this cache has processed that term */
    std::map< Node, bool > d_search_val_proc;
  };
  // anchor -> cache
  std::map< Node, SearchCache > d_cache;
  /** a sygus sampler object for each anchor
   *
   * This is used for the sygusRewVerify() option to verify the correctness of
   * the rewriter.
   */
  std::map<Node, quantifiers::SygusSampler> d_sampler;
  Node d_null;
  void assertTesterInternal( int tindex, TNode n, Node exp, std::vector< Node >& lemmas );
  // register search term
  void registerSearchTerm( TypeNode tn, unsigned d, Node n, bool topLevel, std::vector< Node >& lemmas );
  bool registerSearchValue( Node a, Node n, Node nv, unsigned d, std::vector< Node >& lemmas );
  void registerSymBreakLemma( TypeNode tn, Node lem, unsigned sz, Node e, std::vector< Node >& lemmas );
  void addSymBreakLemmasFor( TypeNode tn, Node t, unsigned d, Node e, std::vector< Node >& lemmas );
  void addSymBreakLemmasFor( TypeNode tn, Node t, unsigned d, std::vector< Node >& lemmas );
  void addSymBreakLemma( TypeNode tn, Node lem, TNode x, TNode n, unsigned lem_sz, unsigned n_depth, std::vector< Node >& lemmas );
private:
  std::map< Node, Node > d_rlv_cond;
  Node getRelevancyCondition( Node n );
private:
  std::map< TypeNode, std::map< int, std::map< unsigned, Node > > > d_simple_sb_pred;
  std::map< TypeNode, Node > d_free_var;
  // user-context dependent if sygus-incremental
  std::map< Node, unsigned > d_simple_proc;
  //get simple symmetry breaking predicate
  Node getSimpleSymBreakPred( TypeNode tn, int tindex, unsigned depth );
  TNode getFreeVar( TypeNode tn );
  Node getTermOrderPredicate( Node n1, Node n2 );
private:
  //should be user-context dependent if sygus in incremental mode
  std::map< Node, bool > d_register_st;
  void registerSizeTerm( Node e, std::vector< Node >& lemmas );
  class SearchSizeInfo {
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
public:
  SygusSymBreakNew( TheoryDatatypes * td, quantifiers::TermDbSygus * tds, context::Context* c );
  ~SygusSymBreakNew();
  /** add tester */
  void assertTester( int tindex, TNode n, Node exp, std::vector< Node >& lemmas );
  void assertFact( Node n, bool polarity, std::vector< Node >& lemmas );
  void preRegisterTerm( TNode n, std::vector< Node >& lemmas  );
  void check( std::vector< Node >& lemmas );
  void getPossibleCons( const Datatype& dt, TypeNode tn, std::vector< bool >& pcons );
public:
  Node getNextDecisionRequest( unsigned& priority, std::vector< Node >& lemmas );
};

}
}
}

#endif

