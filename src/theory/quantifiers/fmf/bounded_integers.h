/*********************                                                        */
/*! \file bounded_integers.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
**/

#include "cvc4_private.h"

#ifndef CVC4__BOUNDED_INTEGERS_H
#define CVC4__BOUNDED_INTEGERS_H

#include "theory/quantifiers/quant_util.h"

#include "context/cdhashmap.h"
#include "context/context.h"
#include "expr/attribute.h"

namespace CVC4 {
namespace theory {

class RepSetIterator;

/**
 * Attribute set to 1 for literals that comprise the bounds of a quantified
 * formula. For example, for:
 *   forall x. ( 0 <= x ^ x <= n ) => P( x )
 * the literals 0 <= x and x <= n are marked 1.
 */
struct BoundIntLitAttributeId
{
};
typedef expr::Attribute<BoundIntLitAttributeId, uint64_t> BoundIntLitAttribute;

namespace quantifiers {

class BoundedIntegers : public QuantifiersModule
{
  typedef context::CDHashMap<Node, bool, NodeHashFunction> NodeBoolMap;
  typedef context::CDHashMap<Node, int, NodeHashFunction> NodeIntMap;
  typedef context::CDHashMap<Node, Node, NodeHashFunction> NodeNodeMap;
  typedef context::CDHashMap<int, bool> IntBoolMap;
private:
  //for determining bounds
  bool hasNonBoundVar( Node f, Node b, std::map< Node, bool >& visited );
  bool hasNonBoundVar( Node f, Node b );
  /** The bound type for each quantified formula, variable pair */
  std::map<Node, std::map<Node, BoundVarType>> d_bound_type;
  /**
   * The ordered list of variables that are finitely bound, for each quantified
   * formulas. Variables that occur later in this list may depend on having
   * finite bounds for variables earlier in this list.
   */
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
   * witness x. (|S| <= n OR ( x in S AND
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
public:
  BoundedIntegers( context::Context* c, QuantifiersEngine* qe );
  virtual ~BoundedIntegers();

  void presolve() override;
  bool needsCheck(Theory::Effort e) override;
  void check(Theory::Effort e, QEffort quant_e) override;
  void checkOwnership(Node q) override;
  /**
   * Is v a variable of quantified formula q that this class has inferred to
   * have a finite bound?
   */
  bool isBound(Node q, Node v) const;
  /**
   * Get the type of bound that was inferred for variable v of quantified
   * formula q, or BOUND_NONE if no bound was inferred.
   */
  BoundVarType getBoundVarType(Node q, Node v) const;
  /**
   * Get the indices of bound variables, in the order they should be processed
   * in a RepSetIterator. For example, for q:
   *   forall xyz. 0 <= x < 5 ^ 0 <= z <= x+7 => P(x,y,z)
   * this would add {1,3} to the vector indices, indicating that x has a finite
   * bound, z has a finite bound assuming x has a finite bound, and y does not
   * have a finite bound.
   */
  void getBoundVarIndices(Node q, std::vector<unsigned>& indices) const;
  /**
   * Get bound elements
   *
   * This gets the (finite) enumeration of the range of variable v of quantified
   * formula q and adds it into the vector elements in the context of the
   * iteration being performed by rsi. It returns true if it could successfully
   * determine this range.
   *
   * This method determines the range of a variable depending on the current
   * state of the iterator rsi and flag initial (which is true when rsi is
   * being initialized). For example, if q is:
   *   forall xy. 0 <= x < 5 ^ 0 <= y <= x+7 => P(x,y)
   * v is y, and rsi currently maps x to 4, then we add the elements 0...11 to
   * the vector elements.
   */
  bool getBoundElements(RepSetIterator* rsi,
                        bool initial,
                        Node q,
                        Node v,
                        std::vector<Node>& elements);
  /** Identify this module */
  std::string identify() const override { return "BoundedIntegers"; }

 private:
  /**
   * Set that variable v of quantified formula q has a finite bound, where
   * bound_type indicates how that bound was inferred.
   */
  void setBoundedVar(Node f, Node v, BoundVarType bound_type);
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
};

}
}
}

#endif
