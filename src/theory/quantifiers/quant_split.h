/*********************                                                        */
/*! \file quant_split.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief dynamic quantifiers splitting
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANT_SPLIT_H
#define __CVC4__THEORY__QUANT_SPLIT_H

#include "theory/quantifiers_engine.h"
#include "context/cdo.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class QuantDSplit : public QuantifiersModule {
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;
private:
  /** list of relevant quantifiers asserted in the current context */
  std::map< Node, int > d_quant_to_reduce;
  /** whether we have instantiated quantified formulas */
  NodeSet d_added_split;
public:
  QuantDSplit( QuantifiersEngine * qe, context::Context* c );
  /** determine whether this quantified formula will be reduced */
  void preRegisterQuantifier(Node q) override;

  /* whether this module needs to check this round */
  bool needsCheck(Theory::Effort e) override;
  /* Call during quantifier engine's check */
  void check(Theory::Effort e, QEffort quant_e) override;
  /* Called for new quantifiers */
  void registerQuantifier(Node q) override {}
  void assertNode(Node n) override {}
  bool checkCompleteFor(Node q) override;
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  std::string identify() const override { return "QuantDSplit"; }
};

}
}
}

#endif
