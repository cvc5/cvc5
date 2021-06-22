#include "theory/arith/nl/cad/lazard_evaluation.h"

#ifdef CVC5_POLY_IMP

#include "base/check.h"
#include "base/output.h"

namespace cvc5::theory::arith::nl::cad {

/**
 * Do a very simple wrapper around the regular poly::infeasible_regions.
 * Warn the user about doing this.
 * This allows for a graceful fallback (albeit with a warning) if CoCoA is not
 * available.
 */
struct LazardEvaluationState
{
  poly::Assignment d_assignment;
};
LazardEvaluation::LazardEvaluation()
    : d_state(std::make_unique<LazardEvaluationState>())
{
}
LazardEvaluation::~LazardEvaluation() {}

void LazardEvaluation::add(const poly::Variable& var, const poly::Value& val)
{
  d_state->d_assignment.set(var, val);
}

void LazardEvaluation::addFreeVariable(const poly::Variable& var) {}

std::vector<poly::Polynomial> LazardEvaluation::reducePolynomial(
    const poly::Polynomial& p) const
{
  return {p};
}
std::vector<poly::Interval> LazardEvaluation::infeasibleRegions(
    const poly::Polynomial& q, poly::SignCondition sc) const
{
  WarningOnce()
      << "CAD::LazardEvaluation is disabled because CoCoA is not available. "
         "Falling back to regular calculation of infeasible regions."
      << std::endl;
  return poly::infeasible_regions(q, d_state->d_assignment, sc);
}

}  // namespace cvc5::theory::arith::nl::cad

#endif
