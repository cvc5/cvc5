/*********************                                                        */
/*! \file bv_inverter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief inverse rules for bit-vector operators
 **/

#include "cvc4_private.h"

#ifndef CVC4__BV_INVERTER_H
#define CVC4__BV_INVERTER_H

#include <map>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** BvInverterQuery
 *
 * This is a virtual class for queries
 * required by the BvInverter class.
 */
class BvInverterQuery
{
 public:
  BvInverterQuery() {}
  virtual ~BvInverterQuery() {}
  /** returns the current model value of n */
  virtual Node getModelValue(Node n) = 0;
  /** returns a bound variable of type tn */
  virtual Node getBoundVariable(TypeNode tn) = 0;
};

// inverter class
// TODO : move to theory/bv/ if generally useful?
class BvInverter
{
 public:
  BvInverter() {}
  ~BvInverter() {}
  /** get dummy fresh variable of type tn, used as argument for sv */
  Node getSolveVariable(TypeNode tn);

  /**
   * Get path to pv in lit, replace that occurrence by sv and all others by
   * pvs (if pvs is non-null). If return value R is non-null, then :
   *   lit.path = pv R.path = sv
   *   R.path' = pvs for all lit.path' = pv, where path' != path
   *
   * If the flag projectNl is false, we return the null node if the
   * literal lit is non-linear with respect to pv.
   */
  Node getPathToPv(Node lit,
                   Node pv,
                   Node sv,
                   Node pvs,
                   std::vector<unsigned>& path,
                   bool projectNl);

  /**
   * Same as above, but does not linearize lit for pv.
   * Use this version if we know lit is linear wrt pv.
   */
  Node getPathToPv(Node lit, Node pv, std::vector<unsigned>& path)
  {
    return getPathToPv(lit, pv, pv, Node::null(), path, false);
  }

  /** solveBvLit
   *
   * Solve for sv in lit, where lit.path = sv. If this function returns a
   * non-null node t, then sv = t is the solved form of lit.
   *
   * If the BvInverterQuery provided to this function call is null, then
   * the solution returned by this call will not contain WITNESS expressions.
   * If the solved form for lit requires introducing a WITNESS expression,
   * then this call will return null.
   */
  Node solveBvLit(Node sv,
                  Node lit,
                  std::vector<unsigned>& path,
                  BvInverterQuery* m);

 private:
  /** Dummy variables for each type */
  std::map<TypeNode, Node> d_solve_var;

  /** Helper function for getPathToPv */
  Node getPathToPv(Node lit,
                   Node pv,
                   Node sv,
                   std::vector<unsigned>& path,
                   std::unordered_set<TNode, TNodeHashFunction>& visited);

  /** Helper function for getInv.
   *
   * This expects a condition cond where:
   *   (exists x. cond)
   * is a BV tautology where x is getSolveVariable( tn ).
   *
   * It returns a term of the form:
   *   (witness y. cond { x -> y })
   * where y is a bound variable and x is getSolveVariable( tn ).
   *
   * In some cases, we may return a term t if cond implies an equality on
   * the solve variable. For example, if cond is x = t where x is
   * getSolveVariable(tn), then we return t instead of introducing the choice
   * function.
   *
   * This function will return the null node if the BvInverterQuery m provided
   * to this call is null.
   */
  Node getInversionNode(Node cond, TypeNode tn, BvInverterQuery* m);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__BV_INVERTER_H */
