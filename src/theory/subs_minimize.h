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
   * If n { vars -> subs } rewrites to target, this method returns true, and
   * vars[i1], ..., vars[in] are added to rewVars, such that
   * n { vars[i_1] -> subs[i_1], ..., vars[i_n] -> subs[i_n] } also rewrites to
   * target.
   *
   * If n { vars -> subs } does not rewrite to target, this method returns
   * false.
   */
  static bool find(Node n,
                   Node target,
                   const std::vector<Node>& vars,
                   const std::vector<Node>& subs,
                   std::vector<Node>& reqVars);

 private:
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
