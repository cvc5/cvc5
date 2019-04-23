/*********************                                                        */
/*! \file bounded_integers.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
**/

#include "cvc4_private.h"

#ifndef __CVC4__BOUNDED_INTEGERS_H
#define __CVC4__BOUNDED_INTEGERS_H


#include "theory/quantifiers_engine.h"

#include "context/context.h"
#include "context/context_mm.h"

namespace CVC4 {
namespace theory {

class RepSetIterator;

namespace quantifiers {


class BoundedIntegers : public QuantifiersModule
{
  typedef context::CDHashMap<Node, bool, NodeHashFunction> NodeBoolMap;
  typedef context::CDHashMap<Node, int, NodeHashFunction> NodeIntMap;
  typedef context::CDHashMap<Node, Node, NodeHashFunction> NodeNodeMap;
  typedef context::CDHashMap<int, bool> IntBoolMap;
public:
  enum {
    BOUND_FINITE,
    BOUND_INT_RANGE,
    BOUND_SET_MEMBER,
    BOUND_FIXED_SET,
    BOUND_NONE
  };
private:
  //for determining bounds
  bool isBound( Node f, Node v );
  bool hasNonBoundVar( Node f, Node b, std::map< Node, bool >& visited );
  bool hasNonBoundVar( Node f, Node b );
  //bound type
  std::map< Node, std::map< Node, unsigned > > d_bound_type;
  std::map< Node, std::vector< Node > > d_set;
  std::map< Node, std::map< Node, int > > d_set_nums;
  std::map< Node, std::map< Node, Node > > d_range;
  std::map< Node, std::map< Node, Node > > d_nground_range;
  //integer lower/upper bounds
  std::map< Node, std::map< Node, Node > > d_bounds[2];
  //set membership range
  std::map< Node, std::map< Node, Node > > d_setm_range;
  std::map< Node, std::map< Node, Node > > d_setm_range_lit;
  /** set membership element choice functions
   *
   * For each set S and integer n, d_setm_choice[S][n] is the canonical
   * representation for the (n+1)^th member of set S. It is of the form:
   * choice x. (|S| <= n OR ( x in S AND
   *   distinct( x, d_setm_choice[S][0], ..., d_setm_choice[S][n-1] ) ) )
   */
  std::map<Node, std::vector<Node> > d_setm_choice;
  //fixed finite set range
  std::map< Node, std::map< Node, std::vector< Node > > > d_fixed_set_gr_range;
  std::map< Node, std::map< Node, std::vector< Node > > > d_fixed_set_ngr_range;
  void process( Node q, Node n, bool pol,
                std::map< Node, unsigned >& bound_lit_type_map,
                std::map< int, std::map< Node, Node > >& bound_lit_map,
                std::map< int, std::map< Node, bool > >& bound_lit_pol_map,
                std::map< int, std::map< Node, Node > >& bound_int_range_term,
                std::map< Node, std::vector< Node > >& bound_fixed_set );
  bool processEqDisjunct( Node q, Node n, Node& v, std::vector< Node >& v_cases );
  void processMatchBoundVars( Node q, Node n, std::vector< Node >& bvs, std::map< Node, bool >& visited );
  std::vector< Node > d_bound_quants;
private:
 /**
  * This decision strategy is used for minimizing the value of an integer
  * arithmetic term t. It decides positively on literals of the form
  * t < 0, t <= 0, t <= 1, t <=2, and so on.
  */
 class IntRangeDecisionHeuristic : public DecisionStrategyFmf
 {
  public:
   IntRangeDecisionHeuristic(Node r,
                             context::Context* c,
                             context::Context* u,
                             Valuation valuation,
                             bool isProxy);
   /** make the n^th literal of this strategy */
   Node mkLiteral(unsigned n) override;
   /** identify */
   std::string identify() const override
   {
     return std::string("bound_int_range");
   }
   /** Returns the current proxy lemma if one exists (see below). */
   Node proxyCurrentRangeLemma();

  private:
   /** The range we are minimizing */
   Node d_range;
   /** a proxy of the range
    *
    * When option::fmfBoundLazy is enabled, this class uses a lazy strategy
    * for enforcing the bounds on term t by using a fresh variable x of type
    * integer. The point of this variable is to serve as a proxy for t, so
    * that we can decide on literals of the form x <= c instead of t <= c. The
    * advantage of this is that we avoid unfairness, say, if t is constrained
    * to be strictly greater c. Then, at full effort check, we add "proxy
    * lemmas" of the form: (t <= c) <=> (x <= c) for the current minimal
    * upper bound c for x.
    */
   Node d_proxy_range;
   /** ranges that have been proxied
    *
    * This is a user-context-dependent cache that stores which value we have
    * added proxy lemmas for.
    */
   IntBoolMap d_ranges_proxied;
  };
private:
  //information for minimizing ranges
  std::vector< Node > d_ranges;
  /** Decision heuristics for each integer range */
  std::map<Node, std::unique_ptr<IntRangeDecisionHeuristic>> d_rms;

 private:
  //class to store whether bounding lemmas have been added
  class BoundInstTrie
  {
  public:
    std::map< Node, BoundInstTrie > d_children;
    bool hasInstantiated( std::vector< Node > & vals, int index = 0, bool madeNew = false ){
      if( index>=(int)vals.size() ){
        return !madeNew;
      }else{
        Node n = vals[index];
        if( d_children.find(n)==d_children.end() ){
          madeNew = true;
        }
        return d_children[n].hasInstantiated(vals,index+1,madeNew);
      }
    }
  };
  std::map< Node, std::map< Node, BoundInstTrie > > d_bnd_it;
private:
  
  void setBoundedVar( Node f, Node v, unsigned bound_type );
public:
  BoundedIntegers( context::Context* c, QuantifiersEngine* qe );
  virtual ~BoundedIntegers();

  void presolve() override;
  bool needsCheck(Theory::Effort e) override;
  void check(Theory::Effort e, QEffort quant_e) override;
  void checkOwnership(Node q) override;
  bool isBoundVar( Node q, Node v ) { return std::find( d_set[q].begin(), d_set[q].end(), v )!=d_set[q].end(); }
  unsigned getBoundVarType( Node q, Node v );
  unsigned getNumBoundVars( Node q ) { return d_set[q].size(); }
  Node getBoundVar( Node q, int i ) { return d_set[q][i]; }
private:
  //for integer range
  Node getLowerBound( Node q, Node v ){ return d_bounds[0][q][v]; }
  Node getUpperBound( Node q, Node v ){ return d_bounds[1][q][v]; }
  void getBounds( Node f, Node v, RepSetIterator * rsi, Node & l, Node & u );
  void getBoundValues( Node f, Node v, RepSetIterator * rsi, Node & l, Node & u );
  bool isGroundRange(Node f, Node v);
  //for set range
  Node getSetRange( Node q, Node v, RepSetIterator * rsi );
  Node getSetRangeValue( Node q, Node v, RepSetIterator * rsi );
  Node matchBoundVar( Node v, Node t, Node e );
  
  bool getRsiSubsitution( Node q, Node v, std::vector< Node >& vars, std::vector< Node >& subs, RepSetIterator * rsi );
public:
  bool getBoundElements( RepSetIterator * rsi, bool initial, Node q, Node v, std::vector< Node >& elements );

  /** Identify this module */
  std::string identify() const override { return "BoundedIntegers"; }
};

}
}
}

#endif
