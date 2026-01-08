/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arithmetic substitution utility.
 */

#ifndef CVC5__THEORY__ARITH__SUBS_H
#define CVC5__THEORY__ARITH__SUBS_H

#include <map>
#include <optional>
#include <vector>

#include "expr/subs.h"
#include "expr/term_context.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

/**
 * applyArith computes the substitution n { subs }, but with the caveat
 * that subterms of n that belong to a theory other than arithmetic are
 * not traversed. In other words, terms that belong to other theories are
 * treated as atomic variables. For example:
 *   (5*f(x) + 7*x ){ x -> 3 } returns 5*f(x) + 7*3.
 *
 * Note that in contrast to the ordinary substitution class, this class allows
 * mixing integers and reals via addArith.
 */
class ArithSubs : public Subs
{
 public:
  /** Add v -> s to the substitution */
  void addArith(const Node& v, const Node& s);
  /**
   * Return the result of this substitution on n.
   * @param n The node to apply the substitution
   * @param traverseNlMult Whether to traverse applications of NONLINEAR_MULT.
   */
  Node applyArith(const Node& n, bool traverseNlMult = true) const;
  /**
   * Should traverse, returns true if the above method traverses n.
   */
  static bool shouldTraverse(const Node& n, bool traverseNlMult = true);
  /**
   * Check if the node n has an arithmetic subterm t.
   * @param n The node to search in
   * @param t The subterm to search for
   * @param traverseNlMult Whether to traverse applications of NONLINEAR_MULT.
   * @return true iff t is a subterm in n
   */
  static bool hasArithSubterm(TNode n, TNode t, bool traverseNlMult = true);
};

/**
 * Arithmetic substitution term context.
 */
class ArithSubsTermContext : public TermContext
{
 public:
  ArithSubsTermContext(bool traverseMult = true) : d_traverseMult(traverseMult)
  {
  }
  /** The initial value: valid. */
  uint32_t initialValue() const override { return 0; }
  /** Compute the value of the index^th child of t whose hash is tval */
  uint32_t computeValue(TNode t, uint32_t tval, size_t index) const override
  {
    if (tval == 0)
    {
      // if we should not traverse, return 1
      if (!ArithSubs::shouldTraverse(t, d_traverseMult))
      {
        return 1;
      }
      return 0;
    }
    return tval;
  }

 private:
  /** Should we traverse (non-linear) multiplication? */
  bool d_traverseMult;
};

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__SUBS_H */
