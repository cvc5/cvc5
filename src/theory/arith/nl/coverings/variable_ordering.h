/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implements variable orderings tailored to CAD.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__NL__CAD__VARIABLE_ORDERING_H
#define CVC5__THEORY__ARITH__NL__CAD__VARIABLE_ORDERING_H

#ifdef CVC5_POLY_IMP

#include <poly/polyxx.h>

#include "theory/arith/nl/cad/constraints.h"
#include "util/poly_util.h"

namespace cvc5 {
namespace theory {
namespace arith {
namespace nl {
namespace cad {

/** Variable orderings for real variables in the context of CAD. */
enum class VariableOrderingStrategy
{
  /** Dummy ordering by variable ID. */
  BYID,
  /** Triangular as of DOI:10.1145/2755996.2756678 */
  TRIANGULAR,
  /** Brown as of DOI:10.1145/2755996.2756678 */
  BROWN
};

class VariableOrdering
{
 public:
  VariableOrdering();
  ~VariableOrdering();
  std::vector<poly::Variable> operator()(
      const Constraints::ConstraintVector& polys,
      VariableOrderingStrategy vos) const;
};

/**
 * Retrieves variable information for all variables with the given polynomials.
 * If with_totals is set, the last element of the vector contains totals as
 * computed by get_variable_information if no variable is specified.
 */
std::vector<poly_utils::VariableInformation> collectInformation(
    const Constraints::ConstraintVector& polys, bool with_totals = false);

}  // namespace cad
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif

#endif
