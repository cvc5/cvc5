/*********************                                                        */
/*! \file ext_theory_callback.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The extended theory callback for non-linear arithmetic
 **/

#ifndef CVC4__THEORY__ARITH__NL__EXT_THEORY_CALLBACK_H
#define CVC4__THEORY__ARITH__NL__EXT_THEORY_CALLBACK_H

#include "expr/node.h"
#include "theory/ext_theory.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

class NlExtTheoryCallback : public ExtTheoryCallback
{
 public:
  NlExtTheoryCallback(eq::EqualityEngine* ee);
  ~NlExtTheoryCallback() {}
  /** Get current substitution
   *
   * This function and the one below are
   * used for context-dependent
   * simplification, see Section 3.1 of
   * "Designing Theory Solvers with Extensions"
   * by Reynolds et al. FroCoS 2017.
   *
   * effort : an identifier indicating the stage where
   *          we are performing context-dependent simplification,
   * vars : a set of arithmetic variables.
   *
   * This function populates subs and exp, such that for 0 <= i < vars.size():
   *   ( exp[vars[i]] ) => vars[i] = subs[i]
   * where exp[vars[i]] is a set of assertions
   * that hold in the current context. We call { vars -> subs } a "derivable
   * substituion" (see Reynolds et al. FroCoS 2017).
   */
  bool getCurrentSubstitution(int effort,
                              const std::vector<Node>& vars,
                              std::vector<Node>& subs,
                              std::map<Node, std::vector<Node>>& exp) override;
  /** Is the term n in reduced form?
   *
   * Used for context-dependent simplification.
   *
   * effort : an identifier indicating the stage where
   *          we are performing context-dependent simplification,
   * on : the original term that we reduced to n,
   * exp : an explanation such that ( exp => on = n ).
   *
   * We return a pair ( b, exp' ) such that
   *   if b is true, then:
   *     n is in reduced form
   *     if exp' is non-null, then ( exp' => on = n )
   * The second part of the pair is used for constructing
   * minimal explanations for context-dependent simplifications.
   */
  bool isExtfReduced(int effort,
                     Node n,
                     Node on,
                     std::vector<Node>& exp) override;

 private:
  /** The underlying equality engine. */
  eq::EqualityEngine* d_ee;
  /** Commonly used nodes */
  Node d_zero;
};

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__ARITH__NL__EXT_THEORY_CALLBACK_H */
