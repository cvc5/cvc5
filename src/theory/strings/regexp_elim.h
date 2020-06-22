/*********************                                                        */
/*! \file regexp_elim.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Techniques for eliminating regular expressions
 **
 **/

#include "cvc4_private.h"
#ifndef CVC4__THEORY__STRINGS__REGEXP_ELIM_H
#define CVC4__THEORY__STRINGS__REGEXP_ELIM_H

#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace strings {

/** Regular expression membership elimination
 *
 * This class implements techniques for reducing regular expression memberships
 * to bounded integer quantifiers + extended function constraints.
 *
 * It is used by TheoryStrings during ppRewrite.
 */
class RegExpElimination
{
 public:
  RegExpElimination();
  /** eliminate membership
   *
   * This method takes as input a regular expression membership atom of the
   * form (str.in.re x R). If this method returns a non-null node ret, then ret
   * is equivalent to atom.
   */
  static Node eliminate(Node atom);

 private:
  /** return elimination
   *
   * This method is called when atom is rewritten to atomElim, and returns
   * atomElim. id is an identifier indicating the reason for the elimination.
   */
  static Node returnElim(Node atom, Node atomElim, const char* id);
  /** elimination for regular expression concatenation */
  static Node eliminateConcat(Node atom);
  /** elimination for regular expression star */
  static Node eliminateStar(Node atom);
}; /* class RegExpElimination */

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__REGEXP_ELIM_H */
