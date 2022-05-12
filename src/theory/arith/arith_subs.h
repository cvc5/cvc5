/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
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
 */
class ArithSubs : public Subs
{
 public:
  /** Return the result of this substitution on n */
  Node apply(Node n) const override;
protected:
  /** check if the substitution v -> s is permitted by this class */
  void checkSubs(const Node& v, const Node& s) override;
};

}
}
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__SUBS_H */
