/*********************                                                        */
/*! \file relevant_domain.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief relevant domain class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__RELEVANT_DOMAIN_H
#define __CVC4__THEORY__QUANTIFIERS__RELEVANT_DOMAIN_H

#include "theory/quantifiers/first_order_model.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class RelevantDomain : public QuantifiersUtil
{
private:
  class RDomain
  {
  public:
    RDomain() : d_parent( NULL ) {}
    void reset() { d_parent = NULL; d_terms.clear(); }
    RDomain * d_parent;
    std::vector< Node > d_terms;
    void merge( RDomain * r );
    void addTerm( Node t );
    RDomain * getParent();
    void removeRedundantTerms( QuantifiersEngine * qe );
    bool hasTerm( Node n ) { return std::find( d_terms.begin(), d_terms.end(), n )!=d_terms.end(); }
  };
  std::map< Node, std::map< int, RDomain * > > d_rel_doms;
  std::map< RDomain *, Node > d_rn_map;
  std::map< RDomain *, int > d_ri_map;
  QuantifiersEngine* d_qe;
  FirstOrderModel* d_model;
  void computeRelevantDomain( Node q, Node n, bool hasPol, bool pol );
  void computeRelevantDomainOpCh( RDomain * rf, Node n );
  bool d_is_computed;
  
  //what each literal does
  class RDomainLit {
  public:
    RDomainLit() : d_merge(false){
      d_rd[0] = NULL;
      d_rd[1] = NULL;
    }
    ~RDomainLit(){}
    bool d_merge;
    RDomain * d_rd[2];
    std::vector< Node > d_val;
  };
  std::map< bool, std::map< bool, std::map< Node, RDomainLit > > > d_rel_dom_lit;
  void computeRelevantDomainLit( Node q, bool hasPol, bool pol, Node n );
public:
  RelevantDomain( QuantifiersEngine* qe, FirstOrderModel* m );
  virtual ~RelevantDomain();
  /* reset */
  bool reset( Theory::Effort e );
  /** identify */
  std::string identify() const { return "RelevantDomain"; }
  //compute the relevant domain
  void compute();

  RDomain * getRDomain( Node n, int i, bool getParent = true );
};/* class RelevantDomain */


}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__RELEVANT_DOMAIN_H */
