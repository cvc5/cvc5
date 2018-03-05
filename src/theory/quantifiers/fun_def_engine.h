/*********************                                                        */
/*! \file fun_def_engine.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Specialized techniques for (recursively) defined functions
 **/

#include "cvc4_private.h"

#ifndef __CVC4__QUANTIFIERS_FUN_DEF_ENGINE_H
#define __CVC4__QUANTIFIERS_FUN_DEF_ENGINE_H

#include <iostream>
#include <string>
#include <vector>
#include <map>
#include "expr/node.h"
#include "expr/type_node.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

//module for handling (recursively) defined functions
class FunDefEngine : public QuantifiersModule {
private:

public:
  FunDefEngine( QuantifiersEngine * qe, context::Context* c );
  ~FunDefEngine(){}

  /* whether this module needs to check this round */
  bool needsCheck(Theory::Effort e) override;
  /* reset at a round */
  void reset_round(Theory::Effort e) override;
  /* Call during quantifier engine's check */
  void check(Theory::Effort e, QEffort quant_e) override;
  /* Called for new quantifiers */
  void registerQuantifier(Node q) override;
  /** called for everything that gets asserted */
  void assertNode(Node n) override;
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  std::string identify() const override { return "FunDefEngine"; }
};


}
}
}

#endif
