/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utils for counterexample-guided quantifier instantiation.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__CEG_UTILS_H
#define CVC5__THEORY__QUANTIFIERS__CEG_UTILS_H

#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/inference_id.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * Descriptions of the types of constraints that a term was solved for in.
 */
enum CegTermType
{
  // invalid
  CEG_TT_INVALID,
  // term was the result of solving an equality
  CEG_TT_EQUAL,
  // term was the result of solving a non-strict lower bound x >= t
  CEG_TT_LOWER,
  // term was the result of solving a strict lower bound x > t
  CEG_TT_LOWER_STRICT,
  // term was the result of solving a non-strict upper bound x <= t
  CEG_TT_UPPER,
  // term was the result of solving a strict upper bound x < t
  CEG_TT_UPPER_STRICT,
};
/** make (non-strict term type) c a strict term type */
CegTermType mkStrictCTT(CegTermType c);
/** negate c (lower/upper bounds are swapped) */
CegTermType mkNegateCTT(CegTermType c);
/** is c a strict term type? */
bool isStrictCTT(CegTermType c);
/** is c a lower bound? */
bool isLowerBoundCTT(CegTermType c);
/** is c an upper bound? */
bool isUpperBoundCTT(CegTermType c);

/** Term Properties
 *
 * Stores properties for a variable to solve for in counterexample-guided
 * instantiation.
 *
 * For LIA, this includes the coefficient of the variable, and the bound type
 * for the variable.
 */
class TermProperties {
 public:
  TermProperties() : d_type(CEG_TT_EQUAL) {}
  virtual ~TermProperties() {}

  /**
   * Type for the solution term. For arithmetic this corresponds to bound type
   * of the constraint that the constraint the term was solved for in.
   */
  CegTermType d_type;
  // for arithmetic
  Node d_coeff;
  // get cache node
  // we consider terms + TermProperties that are unique up to their cache node
  // (see constructInstantiationInc)
  Node getCacheNode() const { return d_coeff; }
  // is non-basic
  bool isBasic() const { return d_coeff.isNull(); }
  // get modified term
  Node getModifiedTerm(Node pv) const
  {
    if( !d_coeff.isNull() ){
      return NodeManager::currentNM()->mkNode( kind::MULT, d_coeff, pv );
    }else{
      return pv;
    }
  }
  // compose property, should be such that: 
  //   p.getModifiedTerm( this.getModifiedTerm( x ) ) = this_updated.getModifiedTerm( x )
  void composeProperty(TermProperties& p);
};

/** Solved form
 *  This specifies a substitution:
 *  { d_props[i].getModifiedTerm(d_vars[i]) -> d_subs[i] | i = 0...|d_vars| }
 */
class SolvedForm {
public:
  // list of variables
  std::vector< Node > d_vars;
  // list of terms that they are substituted to
  std::vector< Node > d_subs;
  // properties for each variable
  std::vector< TermProperties > d_props;
  // the variables that have non-basic information regarding how they are substituted
  //   an example is for linear arithmetic, we store "substitution with coefficients".
  std::vector<Node> d_non_basic;
  // push the substitution pv_prop.getModifiedTerm(pv) -> n
  void push_back(Node pv, Node n, TermProperties& pv_prop);
  // pop the substitution pv_prop.getModifiedTerm(pv) -> n
  void pop_back(Node pv, Node n, TermProperties& pv_prop);
  // is this solved form empty?
  bool empty() { return d_vars.empty(); }
public:
  // theta values (for LIA, see Section 4 of Reynolds/King/Kuncak FMSD 2017)
  std::vector< Node > d_theta;
  // get the current value for theta (for LIA, see Section 4 of Reynolds/King/Kuncak FMSD 2017)
  Node getTheta() {
    if( d_theta.empty() ){
      return Node::null();
    }else{
      return d_theta[d_theta.size()-1];
    }
  }
};

/** instantiation effort levels
 *
 * This effort is used to stratify the construction of
 * instantiations for some theories that may result to
 * using model value instantiations.
 */
enum CegInstEffort
{
  // uninitialized
  CEG_INST_EFFORT_NONE,
  // standard effort level
  CEG_INST_EFFORT_STANDARD,
  // standard effort level, but we have used model values
  CEG_INST_EFFORT_STANDARD_MV,
  // full effort level
  CEG_INST_EFFORT_FULL
};

std::ostream& operator<<(std::ostream& os, CegInstEffort e);

/** instantiation phase for variables
 *
 * This indicates the phase in which we constructed
 * a substitution for individual variables.
 */
enum CegInstPhase
{
  // uninitialized
  CEG_INST_PHASE_NONE,
  // instantiation constructed during traversal of equivalence classes
  CEG_INST_PHASE_EQC,
  // instantiation constructed during solving equalities
  CEG_INST_PHASE_EQUAL,
  // instantiation constructed by looking at theory assertions
  CEG_INST_PHASE_ASSERTION,
  // instantiation constructed by querying model value
  CEG_INST_PHASE_MVALUE,
};

std::ostream& operator<<(std::ostream& os, CegInstPhase phase);

/**
 * The handled status of a sort/term/quantified formula, indicating whether
 * counterexample-guided instantiation handles it.
 */
enum CegHandledStatus
{
  // the sort/term/quantified formula is unhandled by cegqi
  CEG_UNHANDLED,
  // the sort/term/quantified formula is partially handled by cegqi
  CEG_PARTIALLY_HANDLED,
  // the sort/term/quantified formula is handled by cegqi
  CEG_HANDLED,
  // the sort/term/quantified formula is handled by cegqi, regardless of
  // additional factors
  CEG_HANDLED_UNCONDITIONAL,
};
std::ostream& operator<<(std::ostream& os, CegHandledStatus status);

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
