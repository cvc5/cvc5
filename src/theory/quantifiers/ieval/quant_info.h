/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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
#include "theory/uf/equality_engine.h"

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
   */
  void initialize(TNode q, Node body);
  //-------------------------- static information
  /**
   * Get the constraints, which maps pattern terms to node corresponding to
   * their constraints for making the quantified formula have a propagating
   * instance. For details on the range of constraints, see d_req.
   */
  const std::map<TNode, bool>& getConstraints() const;
  /** Get the number of unassigned variables */
  size_t getNumUnassignedVars() const;
  /** Decremental unassigned var */
  void decrementUnassignedVar();
  //-------------------------- queries local to round
  /** Is alive? */
  bool isActive() const;
  /** set dead */
  void setActive(bool val);
  /** Set no conflict */
  void setNoConflict();
  /** Is maybe conflict */
  bool isMaybeConflict() const;
  //-------------------------- utilities
  /** Do we traverse this node? */
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
  /** Canonical form of body */
  Node d_body;
  /**
   * The match terms maped to their requirements. A requirement for p can be:
   * (1) Node::null(), saying that the term must be equal to any ground term
   * (2) (not (= p g)), saying that pattern must be disequal from g
   * (3) g, saying that the pattern must be equal to g
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
};

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
