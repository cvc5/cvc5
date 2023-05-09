/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * quantifier util
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANT_UTIL_H
#define CVC5__THEORY__QUANT_UTIL_H

#include <iostream>
#include <map>
#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/incomplete_id.h"
#include "theory/theory.h"

namespace cvc5::internal {
namespace theory {

/** Quantifiers utility
 *
 * This is a lightweight version of a quantifiers module that does not implement
 * methods for checking satisfiability.
 */
class QuantifiersUtil : protected EnvObj
{
 public:
  QuantifiersUtil(Env& env);
  virtual ~QuantifiersUtil(){}
  /**  Called at the beginning of check-sat call. */
  virtual void presolve() {}
  /* reset
   * Called at the beginning of an instantiation round
   * Returns false if the reset failed. When reset fails, the utility should
   * have added a lemma via a call to d_qim.addPendingLemma.
   */
  virtual bool reset(Theory::Effort e) { return true; }
  /* Called for new quantifiers */
  virtual void registerQuantifier(Node q) {}
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  virtual std::string identify() const = 0;
  /** Check complete?
   *
   * Returns false if the utility's reasoning was globally incomplete
   * (e.g. "sat" must be replaced with "incomplete"). If this method returns
   * false, it should update incId to the reason for incompleteness.
   */
  virtual bool checkComplete(IncompleteId& incId) { return true; }
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

  /**
   * Get the polarity of the child^th child of n, assuming its polarity
   * is given by (hasPol, pol). A term has polarity if it is only relevant
   * if asserted with one polarity. Its polarity is (typically) the number
   * of negations it is beneath.
   */
  static void getPolarity(Node n,
                          size_t child,
                          bool hasPol,
                          bool pol,
                          bool& newHasPol,
                          bool& newPol);

  /**
   * Get the entailed polarity of the child^th child of n, assuming its
   * entailed polarity is given by (hasPol, pol). A term has entailed polarity
   * if it must be asserted with a polarity. Its polarity is (typically) the
   * number of negations it is beneath.
   *
   * Entailed polarity and polarity above differ, e.g.:
   *   (and A B): A and B have true polarity and true entailed polarity
   *   (or A B): A and B have true polarity and no entailed polarity
   */
  static void getEntailPolarity(Node n,
                                size_t child,
                                bool hasPol,
                                bool pol,
                                bool& newHasPol,
                                bool& newPol);
};

}
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANT_UTIL_H */
