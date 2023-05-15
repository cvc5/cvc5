/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Info per quantified formula in instantiation evaluator.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__IEVAL__QUANT_INFO_H
#define CVC5__THEORY__QUANTIFIERS__IEVAL__QUANT_INFO_H

#include <map>

#include "context/cdo.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace ieval {

/**
 * Stores all static information for a quantified formula. Also maintains
 * context-dependent state information for the quantified formula when using
 * the instantiation evaluator.
 */
class QuantInfo
{
 public:
  QuantInfo(context::Context* c);
  /**
   * Initialize, called once.
   * @param q The quantified formula
   * @param body The form of the body of q we are considering. This formula may
   * be different from the body of q (i.e. q[1]) if we are canonizing formula
   * bodies.
   */
  void initialize(TNode q, Node body);
  //-------------------------- static information
  /**
   * Get the constraints, which maps (Boolean) pattern terms to a flag
   * corresponding to the required value for making the quantified formula have
   * a propagating instance. For details on the range of constraints, see d_req.
   */
  const std::map<TNode, bool>& getConstraints() const;
  /** Get the number of unassigned variables */
  size_t getNumUnassignedVars() const;
  /** Decremental unassigned var */
  void decrementUnassignedVar();
  //-------------------------- queries local to round
  /**
   * Is active? True if the current substitution for this quantified formula
   * does not generate an redundant instance.
   */
  bool isActive() const;
  /** set active */
  void setActive(bool val);
  /**
   * Is maybe conflict? True if it may be possible to generate a conflicting
   * instance for this quantified formula for the current substituion.
   */
  bool isMaybeConflict() const;
  /** Set no conflict */
  void setNoConflict();
  /**
   * Get the failure constraint. This is a term in the domain of d_req
   * that was the reason why this quantified formula is inactive.
   */
  TNode getFailureConstraint() const;
  /** Set the failure constraint */
  void setFailureConstraint(TNode c);
  //-------------------------- utilities
  /** Do we traverse this node when considering evaluation? */
  static bool isTraverseTerm(TNode n);
  /** Debug print */
  std::string toStringDebug() const;

 private:
  /**
   * Process matching requirement for subterm cur which is a disjunct in the
   * quantified formula of this class.
   */
  void computeMatchReq(TNode cur, std::vector<TNode>& visit);
  /** Add match term that must be (dis)equal from eqc */
  void addMatchTermReq(TNode t, Node eqc, bool isEq);
  //------------------- static
  /** The quantified formula */
  Node d_quant;
  /** The body of the quantified formula, which is provided in initialize. */
  Node d_body;
  /**
   * The match terms mapped to their requirements. A requirement for p is a
   * Boolean, indicating what value the term must be for the body of the
   * quantified formula to be a conflict. Having the opposite value of
   * the requirement implies the instance is redundant.
   */
  std::map<TNode, bool> d_req;
  /** The domain of d_req */
  std::vector<TNode> d_reqTerms;
  //------------------- within search
  /** is alive, false if we know it is not possible to construct a propagating
   * instance for this quantified formula  */
  context::CDO<bool> d_isActive;
  /**
   * False if a constraint was not entailed; a fully assigned quantified
   * formula with this flag set to flag corresponds to one with a propagating
   * instance.
   */
  context::CDO<bool> d_maybeConflict;
  /** Number of unassigned variables */
  context::CDO<size_t> d_unassignedVars;
  /** The failure constraint */
  context::CDO<Node> d_failReq;
};

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
