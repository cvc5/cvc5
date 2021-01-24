/*********************                                                        */
/*! \file inst_strategy.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Instantiation Engine classes
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__INST_STRATEGY_H
#define CVC4__THEORY__QUANTIFIERS__INST_STRATEGY_H

#include <vector>
#include "expr/node.h"
#include "theory/theory.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace quantifiers {

/** instantiation strategy class */
class InstStrategy
{
 public:
  enum Status
  {
    STATUS_UNFINISHED,
    STATUS_UNKNOWN,
  }; /* enum Status */
 protected:
  /** reference to the instantiation engine */
  QuantifiersEngine* d_quantEngine;

 public:
  InstStrategy(QuantifiersEngine* qe) : d_quantEngine(qe) {}
  virtual ~InstStrategy() {}
  /** presolve */
  virtual void presolve() {}
  /** reset instantiation */
  virtual void processResetInstantiationRound(Theory::Effort effort) = 0;
  /** process method, returns a status */
  virtual int process(Node f, Theory::Effort effort, int e) = 0;
  /** identify */
  virtual std::string identify() const { return std::string("Unknown"); }
}; /* class InstStrategy */

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__INSTANTIATION_ENGINE_H */
