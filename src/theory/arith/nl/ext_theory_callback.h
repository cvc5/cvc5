/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The extended theory callback for non-linear arithmetic.
 */

#ifndef CVC5__THEORY__ARITH__NL__EXT_THEORY_CALLBACK_H
#define CVC5__THEORY__ARITH__NL__EXT_THEORY_CALLBACK_H

#include "expr/node.h"
#include "theory/ext_theory.h"

namespace cvc5::internal {
namespace theory {
namespace eq {
class EqualityEngine;
}
namespace arith {
namespace nl {

class NlExtTheoryCallback : public ExtTheoryCallback
{
 public:
  NlExtTheoryCallback(eq::EqualityEngine* ee);
  ~NlExtTheoryCallback() {}
  /**
   * Gets the current substitution, which maps v in vars to a constant c
   * if there is a constant in its equivalence class, or to v itself otherwise.
   * In this case, it adds (= v c) as the explanation for the substitution of v.
   * Returns true if the substitution is non-trivial.
   */
  bool getCurrentSubstitution(int effort,
                              const std::vector<Node>& vars,
                              std::vector<Node>& subs,
                              std::map<Node, std::vector<Node>>& exp) override;
  /**
   * Check whether the extended function `on` which can be simplified to `n`
   * should be considered "reduced". Terms that are considered reduced are
   * guaranteed to have the correct value in models and thus can be ignored
   * if necessary by the theory solver. For example, if (= x 0) and
   * (= (* x y) 0), then (* x y) may be considered reduced. The motivation is
   * to minimize the number of terms that the non-linear solver must consider.
   *
   * This method returns true if
   * (1) the extended term on is not a transcendental function,
   * (2) the top symobl of n does not belong to non-linear arithmetic.
   *
   * For example,
   * if on, n = (* x y), (* 5 y), we return true
   * if on, n = (* x y), 6, we return true
   * if on, n = (* x y z), (* y z), we return false
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

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__NL__EXT_THEORY_CALLBACK_H */
