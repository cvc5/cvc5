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

class QuantifiersState;

/** A status response to process */
enum class InstStrategyStatus
{
  // the strategy is not finished
  STATUS_UNFINISHED,
  // the status of the strategy is unknown
  STATUS_UNKNOWN,
};

/**
 * A base class for instantiation strategies within E-matching.
 */
class InstStrategy
{
 public:
  InstStrategy(QuantifiersEngine* qe, QuantifiersState& qs)
      : d_quantEngine(qe), d_qstate(qs)
  {
  }
  virtual ~InstStrategy() {}
  /** presolve */
  virtual void presolve() {}
  /** reset instantiation */
  virtual void processResetInstantiationRound(Theory::Effort effort) = 0;
  /** process method, returns a status */
  virtual InstStrategyStatus process(Node f, Theory::Effort effort, int e) = 0;
  /** identify */
  virtual std::string identify() const { return std::string("Unknown"); }

 protected:
  /** reference to the instantiation engine */
  QuantifiersEngine* d_quantEngine;
  /** The quantifiers state object */
  QuantifiersState& d_qstate;
}; /* class InstStrategy */

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__INSTANTIATION_ENGINE_H */
