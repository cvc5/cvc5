/*********************                                                        */
/*! \file local_theory_ext.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief local theory extensions util
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__LOCAL_THEORY_EXT_H
#define CVC4__THEORY__LOCAL_THEORY_EXT_H

#include "context/cdo.h"
#include "expr/attribute.h"
#include "expr/node_trie.h"
#include "theory/quantifiers/quant_util.h"

namespace CVC4 {
namespace theory {

/** Attribute true for quantifiers that do not need to be partially instantiated
 */
struct LtePartialInstAttributeId
{
};
typedef expr::Attribute<LtePartialInstAttributeId, bool>
    LtePartialInstAttribute;

namespace quantifiers {

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
  void getPartialInstantiations(std::vector<Node>& conj,
                                Node q,
                                Node bvl,
                                std::vector<Node>& vars,
                                std::vector<Node>& inst,
                                std::vector<TypeNode>& types,
                                TNodeTrie* curr,
                                unsigned pindex,
                                unsigned paindex,
                                unsigned iindex);
  /** get eligible inst variables */
  void getEligibleInstVars( Node n, std::map< Node, bool >& vars );
  
  bool addVariableToPatternList( Node v, std::vector< int >& pat_var_order, std::map< Node, int >& var_order );
public:
  LtePartialInst( QuantifiersEngine * qe, context::Context* c );
  /** determine whether this quantified formula will be reduced */
  void checkOwnership(Node q) override;
  /** was invoked */
  bool wasInvoked() { return d_wasInvoked; }
  
  /* whether this module needs to check this round */
  bool needsCheck(Theory::Effort e) override;
  /* Call during quantifier engine's check */
  void check(Theory::Effort e, QEffort quant_e) override;
  /* check complete */
  bool checkComplete() override { return !d_wasInvoked; }
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  std::string identify() const override { return "LtePartialInst"; }
};

}
}
}

#endif
