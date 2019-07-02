/*********************                                                        */
/*! \file theory_sets_private.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Kshitij Bansal, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sets theory implementation.
 **
 ** Sets theory implementation.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__SETS__THEORY_SETS_PRIVATE_H
#define CVC4__THEORY__SETS__THEORY_SETS_PRIVATE_H

#include "context/cdhashset.h"
#include "context/context.h"
#include "theory/uf/equality_engine.h"
#include "theory/sets/sets_state.h"

namespace CVC4 {
namespace theory {
namespace sets {

class TheorySetsPrivate;
  
class CardinalityExtension {
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;
 public:
  /**
   * Constructs a new instance of the cardinality solver w.r.t. the provided
   * contexts.
   */
  CardinalityExtension(TheorySetsPrivate& p,
                       SetsState& s,
                    eq::EqualityEngine* e,
                    context::Context* c,
                    context::UserContext* u);

  ~CardinalityExtension(){}
  /** check 
   * FIXME
   */
  void check();
 private:
   /** constants */
   Node d_zero;
   /** the theory of sets which owns this */
  TheorySetsPrivate&                   d_parent;
   /** Reference to the state object for the theory of sets */
   SetsState& d_state;
  void checkCardBuildGraph( std::vector< Node >& lemmas );
  void registerCardinalityTerm( Node n, std::vector< Node >& lemmas );
  void checkCardCycles( std::vector< Node >& lemmas );
  void checkCardCyclesRec( Node eqc, std::vector< Node >& curr, std::vector< Node >& exp, std::vector< Node >& lemmas );
  void checkNormalForms( std::vector< Node >& lemmas, std::vector< Node >& intro_sets );
  void checkNormalForm( Node eqc, std::vector< Node >& intro_sets );
  void checkMinCard( std::vector< Node >& lemmas );
  /** element types of sets for which cardinality is enabled */
  std::map<TypeNode, bool> d_t_card_enabled;
  std::map< Node, Node > d_eqc_to_card_term;
  NodeSet d_card_processed;
  std::map< Node, std::vector< Node > > d_card_parent;
  std::map< Node, std::map< Node, std::vector< Node > > > d_ff;
  std::map< Node, std::vector< Node > > d_nf;
  std::map< Node, Node > d_card_base;
  
  std::vector< Node > d_set_eqc;
};/* class CardinalityExtension */


}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__SETS__THEORY_SETS_PRIVATE_H */
