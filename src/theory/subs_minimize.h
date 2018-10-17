/*********************                                                        */
/*! \file subs_minimize.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Substitution minimization.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__SUBS_MINIMIZE_H
#define __CVC4__THEORY__SUBS_MINIMIZE_H

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
   * vars[i1], ..., vars[in] are added to reqVars, such that
   * t { vars[i_1] -> subs[i_1], ..., vars[i_n] -> subs[i_n] } also rewrites to
   * target.
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
   * vars[i1], ..., vars[in] are added to reqVars, and
   * vars[i{n+1}], ..., vars[i{n+m}] are added to impliedVars such that
   * i1...i{n+m} are distinct, and:
   *
   * t { vars[i1]->subs[i1], ..., vars[i{n+k}]->subs[i{n+k}] }
   *   implies
   * vars[i{n+k+1}] = subs[i{n+k+1}]
   *
   * for k = 0, ..., m-1.
   *
   * For example, given (x>0 ^ x = y ^ y = z){ x -> 1, y -> 1, z -> 1, w -> 0 },
   * this method adds { x } to reqVars, and { y, z } to impliedVars.
   */
  static bool findWithImplied(Node t,
                              const std::vector<Node>& vars,
                              const std::vector<Node>& subs,
                              std::vector<Node>& reqVars,
                              std::vector<Node>& impliedVars);

 private:
  /** true node */
  Node d_true;
  /**
   * Helper function for the above functions. The argument computeImplied is
   * whether we are constructing impliedVars.
   */
  bool SubstitutionMinimize::findInternal(Node n,
                                          Node target,
                                          const std::vector<Node>& vars,
                                          const std::vector<Node>& subs,
                                          std::vector<Node>& reqVars,
                                          std::vector<Node>& impliedVars,
                                          bool computeImplied);
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

#endif /* __CVC4__THEORY__SUBS_MINIMIZE_H */
