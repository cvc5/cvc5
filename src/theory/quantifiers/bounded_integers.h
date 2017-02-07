/*********************                                                        */
/*! \file bounded_integers.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
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
#include "context/cdchunk_list.h"

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
  //fixed finite set range
  std::map< Node, std::map< Node, std::vector< Node > > > d_fixed_set_gr_range;
  std::map< Node, std::map< Node, std::vector< Node > > > d_fixed_set_ngr_range;
  void hasFreeVar( Node f, Node n );
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
  class RangeModel {
  public:
    RangeModel(){}
    virtual ~RangeModel(){}
    virtual void initialize() = 0;
    virtual void assertNode(Node n) = 0;
    virtual Node getNextDecisionRequest() = 0;
    virtual bool proxyCurrentRange() = 0;
  };
  class IntRangeModel : public RangeModel {
  private:
    BoundedIntegers * d_bi;
    void allocateRange();
    Node d_proxy_range;
  public:
    IntRangeModel( BoundedIntegers * bi, Node r, context::Context* c, context::Context* u, bool isProxy);
    virtual ~IntRangeModel(){}
    Node d_range;
    int d_curr_max;
    std::map< int, Node > d_range_literal;
    std::map< Node, bool > d_lit_to_pol;
    NodeIntMap d_lit_to_range;
    NodeBoolMap d_range_assertions;
    context::CDO< bool > d_has_range;
    context::CDO< int > d_curr_range;
    IntBoolMap d_ranges_proxied;
    void initialize();
    void assertNode(Node n);
    Node getNextDecisionRequest();
    bool proxyCurrentRange();
  };
private:
  //information for minimizing ranges
  std::vector< Node > d_ranges;
  //map to range model objects
  std::map< Node, RangeModel * > d_rms;
  //literal to range
  std::map< Node, std::vector< Node > > d_lit_to_ranges;
  //list of currently asserted arithmetic literals
  NodeBoolMap d_assertions;
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
  void addLiteralFromRange( Node lit, Node r );
  
  void setBoundedVar( Node f, Node v, unsigned bound_type );
public:
  BoundedIntegers( context::Context* c, QuantifiersEngine* qe );
  virtual ~BoundedIntegers();
  
  void presolve();
  bool needsCheck( Theory::Effort e );
  void check( Theory::Effort e, unsigned quant_e );
  void registerQuantifier( Node q );
  void preRegisterQuantifier( Node q );
  void assertNode( Node n );
  Node getNextDecisionRequest( unsigned& priority );
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
  std::string identify() const { return "BoundedIntegers"; }
};

}
}
}

#endif
