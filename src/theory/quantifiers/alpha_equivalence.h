/*********************                                                        */
/*! \file alpha_equivalence.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Alpha equivalence checking
 **/

#include "cvc4_private.h"

#ifndef __CVC4__ALPHA_EQUIVALENCE_H
#define __CVC4__ALPHA_EQUIVALENCE_H


#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class AlphaEquivalenceNode {
public:
  std::map< Node, std::map< int, AlphaEquivalenceNode > > d_children;
  Node d_quant;
  static Node registerNode( AlphaEquivalenceNode* aen, QuantifiersEngine* qe, Node q, std::vector< Node >& tt, std::vector< int >& arg_index );
};

class AlphaEquivalenceTypeNode {
public:
  std::map< TypeNode, std::map< int, AlphaEquivalenceTypeNode > > d_children;
  AlphaEquivalenceNode d_data;
  static Node registerNode( AlphaEquivalenceTypeNode* aetn,
                            QuantifiersEngine* qe, Node q, Node t, std::vector< TypeNode >& typs, std::map< TypeNode, int >& typ_count, int index = 0 );
};

class AlphaEquivalence {
private:
  QuantifiersEngine* d_qe;
  //per # of variables per type
  AlphaEquivalenceTypeNode d_ae_typ_trie;
public:
  AlphaEquivalence( QuantifiersEngine* qe ) : d_qe( qe ){}
  ~AlphaEquivalence(){}
  /** reduce quantifier, return value (if non-null) is lemma justifying why q ia reducible. */
  Node reduceQuantifier( Node q );
};

}
}
}

#endif
