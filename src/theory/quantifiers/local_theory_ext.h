/*********************                                                        */
/*! \file local_theory_ext.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief local theory extensions util
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__LOCAL_THEORY_EXT_H
#define __CVC4__THEORY__LOCAL_THEORY_EXT_H

#include "theory/quantifiers_engine.h"
#include "context/cdo.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class TermArgTrie;  

class LtePartialInst : public QuantifiersModule {
private:
  // was this module invoked
  bool d_wasInvoked;
  // needs check
  bool d_needsCheck;
  //representatives per type
  std::map< TypeNode, std::vector< Node > > d_reps;
  // should we instantiate quantifier
  std::map< Node, bool > d_do_inst;
  // have we instantiated quantifier
  std::map< Node, bool > d_inst;
  std::map< Node, std::vector< Node > > d_vars;
  std::map< Node, std::vector< int > > d_pat_var_order;
  /** list of relevant quantifiers asserted in the current context */
  std::vector< Node > d_lte_asserts;
  /** reset */
  void reset();
  /** get instantiations */
  void getInstantiations( std::vector< Node >& lemmas );
  void getPartialInstantiations( std::vector< Node >& conj, Node q, Node bvl,
                                 std::vector< Node >& vars, std::vector< Node >& inst, std::vector< TypeNode >& types, TermArgTrie * curr,
                                 unsigned pindex, unsigned paindex, unsigned iindex );
  /** get eligible inst variables */
  void getEligibleInstVars( Node n, std::map< Node, bool >& vars );
  
  bool addVariableToPatternList( Node v, std::vector< int >& pat_var_order, std::map< Node, int >& var_order );
public:
  LtePartialInst( QuantifiersEngine * qe, context::Context* c );
  /** add quantifier : special form of registration */
  bool addQuantifier( Node q );
  /** was invoked */
  bool wasInvoked() { return d_wasInvoked; }
  
  /* whether this module needs to check this round */
  bool needsCheck( Theory::Effort e );
  /* Call during quantifier engine's check */
  void check( Theory::Effort e, unsigned quant_e );
  /* Called for new quantifiers */
  void registerQuantifier( Node q ) {}
  void assertNode( Node n ) {}
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  std::string identify() const { return "LtePartialInst"; }
  
};

}
}
}

#endif
