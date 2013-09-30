/*********************                                                        */
/*! \file relevant_domain.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
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

class RelevantDomain
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
    void removeRedundantTerms( FirstOrderModel * fm );
    bool hasTerm( Node n ) { return std::find( d_terms.begin(), d_terms.end(), n )!=d_terms.end(); }
  };
  std::map< Node, std::map< int, RDomain * > > d_rel_doms;
  std::map< RDomain *, Node > d_rn_map;
  std::map< RDomain *, int > d_ri_map;
  RDomain * getRDomain( Node n, int i );
  QuantifiersEngine* d_qe;
  FirstOrderModel* d_model;
  void computeRelevantDomain( Node n, bool hasPol, bool pol );
public:
  RelevantDomain( QuantifiersEngine* qe, FirstOrderModel* m );
  virtual ~RelevantDomain(){}
  //compute the relevant domain
  void compute();

  Node getRelevantTerm( Node f, int i, Node r );
};/* class RelevantDomain */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__RELEVANT_DOMAIN_H */
