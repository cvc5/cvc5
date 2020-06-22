/*********************                                                        */
/*! \file subs_minimize.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Substitution minimization.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__SUBS_MINIMIZE_H
#define CVC4__THEORY__SUBS_MINIMIZE_H

#include <vector>

#include "expr/node.h"

namespace CVC4 {
namespace theory {

/** SubstitutionMinimize
 *
 * This class is used for finding a minimal substitution under which an
 * evaluation holds.
 */
class SubstitutionMinimize
{
 public:
  SubstitutionMinimize();
  ~SubstitutionMinimize() {}
  /** find
   *
   * If t { vars -> subs } rewrites to target, this method returns true, and
   * vars[i_1], ..., vars[i_n] are added to reqVars, such that i_1, ..., i_n are
   * distinct, and t { vars[i_1] -> subs[i_1], ..., vars[i_n] -> subs[i_n] }
   * rewrites to target.
   *
   * If t { vars -> subs } does not rewrite to target, this method returns
   * false.
   */
  static bool find(Node t,
                   Node target,
                   const std::vector<Node>& vars,
                   const std::vector<Node>& subs,
                   std::vector<Node>& reqVars);
  /** find with implied
   *
   * This method should be called on a formula t.
   *
   * If t { vars -> subs } rewrites to true, this method returns true,
   * vars[i_1], ..., vars[i_n] are added to reqVars, and
   * vars[i_{n+1}], ..., vars[i_{n+m}] are added to impliedVars such that
   * i_1...i_{n+m} are distinct, i_{n+1} < ... < i_{n+m}, and:
   *
   * (1) t { vars[i_1]->subs[i_1], ..., vars[i_{n+k}]->subs[i_{n+k}] } implies
   * vars[i_{n+k+1}] = subs[i_{n+k+1}] for k = 0, ..., m-1.
   *
   * (2) t { vars[i_1] -> subs[i_1], ..., vars[i_{n+m}] -> subs[i_{n+m}] }
   * rewrites to true.
   *
   * For example, given (x>0 ^ x = y ^ y = z){ x -> 1, y -> 1, z -> 1, w -> 0 },
   * this method may add { x } to reqVars, and { y, z } to impliedVars.
   *
   * Notice that the order of variables in vars matters. By the semantics above,
   * variables that appear earlier in the variable list vars are more likely
   * to appear in reqVars, whereas those later in the vars are more likely to
   * appear in impliedVars.
   */
  static bool findWithImplied(Node t,
                              const std::vector<Node>& vars,
                              const std::vector<Node>& subs,
                              std::vector<Node>& reqVars,
                              std::vector<Node>& impliedVars);

 private:
  /** Common helper function for the above functions. */
  static bool findInternal(Node t,
                           Node target,
                           const std::vector<Node>& vars,
                           const std::vector<Node>& subs,
                           std::vector<Node>& reqVars);
  /** is singular arg
   *
   * Returns true if
   *   <k>( ... t_{arg-1}, n, t_{arg+1}...) = c
   * always holds for some constant c.
   */
  static bool isSingularArg(Node n, Kind k, unsigned arg);
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__SUBS_MINIMIZE_H */
