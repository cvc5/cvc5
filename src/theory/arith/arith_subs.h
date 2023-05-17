/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
  /** Return the result of this substitution on n */
  Node applyArith(const Node& n) const;
};

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__SUBS_H */
