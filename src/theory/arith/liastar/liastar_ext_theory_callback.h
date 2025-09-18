/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The extended theory callback for non-linear arithmetic.
 */

#ifndef CVC5__THEORY__ARITH__LIASTAR__EXT_THEORY_CALLBACK_H
#define CVC5__THEORY__ARITH__LIASTAR__EXT_THEORY_CALLBACK_H

#include "expr/node.h"
#include "theory/ext_theory.h"

namespace cvc5::internal {
namespace theory {
namespace eq {
class EqualityEngine;
}
namespace arith {
namespace liastar {

class LiaStarExtTheoryCallback : public ExtTheoryCallback
{
 public:
  LiaStarExtTheoryCallback(eq::EqualityEngine* ee);
  ~LiaStarExtTheoryCallback() {}
  /*
   * Get current substitution at an effort
   * @param effort The effort identifier
   * @param vars The variables to get a substitution for
   * @param subs The terms to substitute for variables, in order. This vector
   * should be updated to one the same size as vars.
   * @param exp The map containing the explanation for each variable. Together
   * with subs, we have that:
   *   ( exp[vars[i]] => vars[i] = subs[i] ) holds for all i
   * @return true if any (non-identity) substitution was added to subs.
   */
  bool getCurrentSubstitution(int effort,
                              const std::vector<Node>& vars,
                              std::vector<Node>& subs,
                              std::map<Node, std::vector<Node> >& exp) override;
  /*
   * Is extended function n reduced? This returns true if n is reduced to a
   * form that requires no further interaction from the theory.
   *
   * @param effort The effort identifier
   * @param n The term to reduce
   * @param on The original form of n, before substitution
   * @param exp The explanation of on = n
   * @param id If this method returns true, then id is updated to the reason
   * why n was reduced.
   * @return true if n is reduced.
   */
  bool isExtfReduced(int effort,
                     Node n,
                     Node on,
                     std::vector<Node>& exp,
                     ExtReducedId& id) override;

 private:
  /** The underlying equality engine. */
  eq::EqualityEngine* d_ee;
};

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__LIASTAR__EXT_THEORY_CALLBACK_H */
