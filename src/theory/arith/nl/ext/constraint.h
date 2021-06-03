/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for non-linear constraints.
 */

#ifndef CVC5__THEORY__ARITH__NL__EXT__CONSTRAINT_H
#define CVC5__THEORY__ARITH__NL__EXT__CONSTRAINT_H

#include <map>
#include <vector>

#include "expr/kind.h"
#include "expr/node.h"

namespace cvc5 {
namespace theory {
namespace arith {
namespace nl {

class MonomialDb;

/** constraint information
 *
 * The struct ( d_rhs, d_coeff, d_type ) represents that a literal is of the
 * form (d_coeff * x) <d_type> d_rhs.
 */
struct ConstraintInfo
{
 public:
  /** The term on the right hand side of the constraint */
  Node d_rhs;
  /** The coefficent */
  Node d_coeff;
  /** The type (relation) of the constraint */
  Kind d_type;
}; /* struct ConstraintInfo */

/** A database for constraints */
class ConstraintDb
{
 public:
  ConstraintDb(MonomialDb& mdb);
  ~ConstraintDb() {}
  /** register constraint
   *
   * This ensures that atom is in the domain of the constraints maintained by
   * this database.
   */
  void registerConstraint(Node atom);
  /** get constraints
   *
   * Returns a map m such that whenever
   * m[lit][x] = ( r, coeff, k ), then
   * ( lit <=>  (coeff * x) <k> r )
   */
  const std::map<Node, std::map<Node, ConstraintInfo> >& getConstraints();
  /** Returns true if m is of maximal degree in atom
   *
   * For example, for atom x^2 + x*y + y >=0, the monomials x^2 and x*y
   * are of maximal degree (2).
   */
  bool isMaximal(Node atom, Node m) const;

 private:
  /** Reference to a monomial database */
  MonomialDb& d_mdb;
  /** List of all constraints */
  std::vector<Node> d_constraints;
  /** Is maximal degree */
  std::map<Node, std::map<Node, bool> > d_c_info_maxm;
  /** Constraint information */
  std::map<Node, std::map<Node, ConstraintInfo> > d_c_info;
};

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__ARITH__NL_SOLVER_H */
