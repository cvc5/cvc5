/*********************                                                        */
/*! \file quant_util.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief quantifier util
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANT_UTIL_H
#define CVC4__THEORY__QUANT_UTIL_H

#include <iostream>
#include <map>
#include <vector>

#include "expr/node.h"
#include "theory/theory.h"

namespace CVC4 {
namespace theory {

/** Quantifiers utility
 *
 * This is a lightweight version of a quantifiers module that does not implement
 * methods for checking satisfiability.
 */
class QuantifiersUtil {
public:
  QuantifiersUtil(){}
  virtual ~QuantifiersUtil(){}
  /* reset
   * Called at the beginning of an instantiation round
   * Returns false if the reset failed. When reset fails, the utility should
   * have added a lemma via a call to d_qim.addPendingLemma.
   */
  virtual bool reset( Theory::Effort e ) = 0;
  /* Called for new quantifiers */
  virtual void registerQuantifier(Node q) = 0;
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  virtual std::string identify() const = 0;
  /** Check complete?
   *
   * Returns false if the utility's reasoning was globally incomplete
   * (e.g. "sat" must be replaced with "incomplete").
   */
  virtual bool checkComplete() { return true; }
};

class QuantPhaseReq
{
private:
  /** helper functions compute phase requirements */
  void computePhaseReqs( Node n, bool polarity, std::map< Node, int >& phaseReqs );
public:
  QuantPhaseReq(){}
  QuantPhaseReq( Node n, bool computeEq = false );
  ~QuantPhaseReq(){}
  void initialize( Node n, bool computeEq );
  /** is phase required */
  bool isPhaseReq( Node lit ) { return d_phase_reqs.find( lit )!=d_phase_reqs.end(); }
  /** get phase requirement */
  bool getPhaseReq( Node lit ) { return d_phase_reqs.find( lit )==d_phase_reqs.end() ? false : d_phase_reqs[ lit ]; }
  /** phase requirements for each quantifier for each instantiation literal */
  std::map< Node, bool > d_phase_reqs;
  std::map< Node, bool > d_phase_reqs_equality;
  std::map< Node, Node > d_phase_reqs_equality_term;

  static void getPolarity( Node n, int child, bool hasPol, bool pol, bool& newHasPol, bool& newPol );
  static void getEntailPolarity( Node n, int child, bool hasPol, bool pol, bool& newHasPol, bool& newPol );
};

/** Types of bounds that can be inferred for quantified formulas */
enum BoundVarType
{
  // a variable has a finite bound because it has finite cardinality
  BOUND_FINITE,
  // a variable has a finite bound because it is in an integer range, e.g.
  //   forall x. u <= x <= l => P(x)
  BOUND_INT_RANGE,
  // a variable has a finite bound because it is a member of a set, e.g.
  //   forall x. x in S => P(x)
  BOUND_SET_MEMBER,
  // a variable has a finite bound because only a fixed set of terms are
  // relevant for it in the domain of the quantified formula, e.g.
  //   forall x. ( x = t1 OR ... OR x = tn ) => P(x)
  BOUND_FIXED_SET,
  // a bound has not been inferred for the variable
  BOUND_NONE
};
}
}

#endif /* CVC4__THEORY__QUANT_UTIL_H */
