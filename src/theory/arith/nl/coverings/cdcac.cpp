/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implements the CDCAC approach as described in
 * https://arxiv.org/pdf/2003.05633.pdf.
 */

#include "theory/arith/nl/coverings/cdcac.h"

#ifdef CVC5_POLY_IMP

#include "options/arith_options.h"
#include "theory/arith/nl/coverings/lazard_evaluation.h"
#include "theory/arith/nl/coverings/projections.h"
#include "theory/arith/nl/coverings/variable_ordering.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/rewriter.h"
#include "util/resource_manager.h"

using namespace cvc5::internal::kind;

namespace std {
/** Generic streaming operator for std::vector. */
template <typename T>
std::ostream& operator<<(std::ostream& os, const std::vector<T>& v)
{
  cvc5::internal::container_to_stream(os, v);
  return os;
}
}  // namespace std

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {
namespace coverings {

CDCAC::CDCAC(Env& env, const std::vector<poly::Variable>& ordering)
    : EnvObj(env), d_variableOrdering(ordering)
{
  if (d_env.isTheoryProofProducing())
  {
    d_proof.reset(new CoveringsProofGenerator(env, userContext()));
  }
}

void CDCAC::reset()
{
  d_constraints.reset();
  d_assignment.clear();
  d_nextIntervalId = 1;
}

void CDCAC::computeVariableOrdering()
{
  // Actually compute the variable ordering
  d_variableOrdering = d_varOrder(d_constraints.getConstraints(),
                                  VariableOrderingStrategy::BROWN);
  Trace("cdcac") << "Variable ordering is now " << d_variableOrdering
                 << std::endl;

  // Write variable ordering back to libpoly.
  lp_variable_order_t* vo = poly::Context::get_context().get_variable_order();
  lp_variable_order_clear(vo);
  for (const auto& v : d_variableOrdering)
  {
    lp_variable_order_push(vo, v.get_internal());
  }
}

void CDCAC::retrieveInitialAssignment(NlModel& model, const Node& ran_variable)
{
  if (options().arith.nlCovLinearModel == options::nlCovLinearModelMode::NONE) return;
  d_initialAssignment.clear();
  Trace("cdcac") << "Retrieving initial assignment:" << std::endl;
  for (const auto& var : d_variableOrdering)
  {
    Node v = getConstraints().varMapper()(var);
    Node val = model.computeConcreteModelValue(v);
    poly::Value value = node_to_value(val, ran_variable);
    Trace("cdcac") << "\t" << var << " = " << value << std::endl;
    d_initialAssignment.emplace_back(value);
  }
}
Constraints& CDCAC::getConstraints() { return d_constraints; }
const Constraints& CDCAC::getConstraints() const { return d_constraints; }

const poly::Assignment& CDCAC::getModel() const { return d_assignment; }

const std::vector<poly::Variable>& CDCAC::getVariableOrdering() const
{
  return d_variableOrdering;
}

std::vector<CACInterval> CDCAC::getUnsatIntervals(std::size_t cur_variable)
{
  std::vector<CACInterval> res;
  LazardEvaluation le(statisticsRegistry());
  prepareRootIsolation(le, cur_variable);
  for (const auto& c : d_constraints.getConstraints())
  {
    const poly::Polynomial& p = std::get<0>(c);
    poly::SignCondition sc = std::get<1>(c);
    const Node& n = std::get<2>(c);

    if (main_variable(p) != d_variableOrdering[cur_variable])
    {
      // Constraint is in another variable, ignore it.
      continue;
    }

    Trace("cdcac") << "Infeasible intervals for " << p << " " << sc
                   << " 0 over " << d_assignment << std::endl;
    std::vector<poly::Interval> intervals;
    if (options().arith.nlCovLifting
        == options::nlCovLiftingMode::LAZARD)
    {
      intervals = le.infeasibleRegions(p, sc);
      if (TraceIsOn("cdcac"))
      {
        auto reference = poly::infeasible_regions(p, d_assignment, sc);
        Trace("cdcac") << "Lazard: " << intervals << std::endl;
        Trace("cdcac") << "Regular: " << reference << std::endl;
      }
    }
    else
    {
      intervals = poly::infeasible_regions(p, d_assignment, sc);
    }
    for (const auto& i : intervals)
    {
      Trace("cdcac") << "-> " << i << std::endl;
      PolyVector l, u, m, d;
      m.add(p);
      m.pushDownPolys(d, d_variableOrdering[cur_variable]);
      if (!is_minus_infinity(get_lower(i))) l = m;
      if (!is_plus_infinity(get_upper(i))) u = m;
      res.emplace_back(CACInterval{d_nextIntervalId++, i, l, u, m, d, {n}});
      if (isProofEnabled())
      {
        d_proof->addDirect(
            d_constraints.varMapper()(d_variableOrdering[cur_variable]),
            d_constraints.varMapper(),
            p,
            d_assignment,
            sc,
            i,
            n,
            res.back().d_id);
      }
    }
  }
  pruneRedundantIntervals(res);
  return res;
}

bool CDCAC::sampleOutsideWithInitial(const std::vector<CACInterval>& infeasible,
                                     poly::Value& sample,
                                     std::size_t cur_variable)
{
  if (options().arith.nlCovLinearModel != options::nlCovLinearModelMode::NONE
      && cur_variable < d_initialAssignment.size())
  {
    const poly::Value& suggested = d_initialAssignment[cur_variable];
    for (const auto& i : infeasible)
    {
      if (poly::contains(i.d_interval, suggested))
      {
        if (options().arith.nlCovLinearModel == options::nlCovLinearModelMode::INITIAL)
        {
          d_initialAssignment.clear();
        }
        return sampleOutside(infeasible, sample);
      }
    }
    Trace("cdcac") << "Using suggested initial value" << std::endl;
    sample = suggested;
    return true;
  }
  return sampleOutside(infeasible, sample);
}

namespace {

/**
 * This method follows the projection operator as detailed in algorithm 6 of
 * 10.1016/j.jlamp.2020.100633, which mostly follows the projection operator due
 * to McCallum. It uses all coefficients until one is either constant or does
 * not vanish over the current assignment.
 */
PolyVector requiredCoefficientsOriginal(const poly::Polynomial& p,
                                        const poly::Assignment& assignment)
{
  PolyVector res;
  for (long deg = degree(p); deg >= 0; --deg)
  {
    auto coeff = coefficient(p, deg);
    Assert(poly::is_constant(coeff)
           == lp_polynomial_is_constant(coeff.get_internal()));
    if (poly::is_constant(coeff)) break;
    res.add(coeff);
    if (evaluate_constraint(coeff, assignment, poly::SignCondition::NE))
    {
      break;
    }
  }
  return res;
}

/**
 * This method follows the original projection operator due to Lazard from
 * section 3 of 10.1007/978-1-4612-2628-4_29. It uses the leading and trailing
 * coefficient, and makes some limited efforts to avoid them in certain cases:
 * We avoid the leading coefficient if it is constant. We avoid the trailing
 * coefficient if the leading coefficient does not vanish over the current
 * assignment and the trailing coefficient is not constant.
 */
PolyVector requiredCoefficientsLazard(const poly::Polynomial& p,
                                      const poly::Assignment& assignment)
{
  PolyVector res;
  auto lc = poly::leading_coefficient(p);
  if (poly::is_constant(lc)) return res;
  res.add(lc);
  if (evaluate_constraint(lc, assignment, poly::SignCondition::NE)) return res;
  auto tc = poly::coefficient(p, 0);
  if (poly::is_constant(tc)) return res;
  res.add(tc);
  return res;
}

/**
 * This method follows the enhancements from 10.1007/978-3-030-60026-6_8 for the
 * projection operator due to Lazard, more specifically Section 3.3 and
 * Definition 4. In essence, we can skip the trailing coefficient if we can show
 * that p is not nullified by any n-1 dimensional point. The statement in the
 * paper is slightly more general, but there is no simple way to have such a
 * procedure T here. We simply try to show that T(f) = {} by using the extended
 * rewriter to simplify (and (= f_i 0)) (f_i being the coefficients of f) to
 * false.
 */
PolyVector requiredCoefficientsLazardModified(
    const poly::Polynomial& p,
    const poly::Assignment& assignment,
    VariableMapper& vm,
    Rewriter* rewriter)
{
  PolyVector res;
  auto lc = poly::leading_coefficient(p);
  // if leading coefficient is constant
  if (poly::is_constant(lc)) return res;
  // add leading coefficient
  res.add(lc);
  auto tc = poly::coefficient(p, 0);
  // if trailing coefficient is constant
  if (poly::is_constant(tc)) return res;
  // if leading coefficient does not vanish over the current assignment
  if (evaluate_constraint(lc, assignment, poly::SignCondition::NE)) return res;

  // construct phi := (and (= p_i 0)) with p_i the coefficients of p
  std::vector<Node> conditions;
  auto zero = NodeManager::currentNM()->mkConstReal(Rational(0));
  for (const auto& coeff : poly::coefficients(p))
  {
    conditions.emplace_back(NodeManager::currentNM()->mkNode(
        Kind::EQUAL, nl::as_cvc_polynomial(coeff, vm), zero));
  }
  // if phi is false (i.e. p can not vanish)
  Node rewritten =
      rewriter->extendedRewrite(NodeManager::currentNM()->mkAnd(conditions));
  if (rewritten.isConst())
  {
    Assert(rewritten.getKind() == Kind::CONST_BOOLEAN);
    Assert(!rewritten.getConst<bool>());
    return res;
  }
  // otherwise add trailing coefficient as well
  res.add(tc);
  return res;
}

}  // namespace

PolyVector CDCAC::requiredCoefficients(const poly::Polynomial& p)
{
  if (TraceIsOn("cdcac::projection"))
  {
    Trace("cdcac::projection")
        << "Poly: " << p << " over " << d_assignment << std::endl;
    Trace("cdcac::projection")
        << "Lazard:   " << requiredCoefficientsLazard(p, d_assignment)
        << std::endl;
    Trace("cdcac::projection")
        << "LMod: "
        << requiredCoefficientsLazardModified(
               p, d_assignment, d_constraints.varMapper(), d_env.getRewriter())
        << std::endl;
    Trace("cdcac::projection")
        << "Original: " << requiredCoefficientsOriginal(p, d_assignment)
        << std::endl;
  }
  switch (options().arith.nlCovProjection)
  {
    case options::nlCovProjectionMode::MCCALLUM:
      return requiredCoefficientsOriginal(p, d_assignment);
    case options::nlCovProjectionMode::LAZARD:
      return requiredCoefficientsLazard(p, d_assignment);
    case options::nlCovProjectionMode::LAZARDMOD:
      return requiredCoefficientsLazardModified(
          p, d_assignment, d_constraints.varMapper(), d_env.getRewriter());
    default:
      Assert(false);
      return requiredCoefficientsOriginal(p, d_assignment);
  }
}

PolyVector CDCAC::constructCharacterization(std::vector<CACInterval>& intervals)
{
  Assert(!intervals.empty()) << "A covering can not be empty";
  Trace("cdcac") << "Constructing characterization now" << std::endl;
  PolyVector res;

  for (std::size_t i = 0, n = intervals.size(); i < n - 1; ++i)
  {
    coverings::makeFinestSquareFreeBasis(intervals[i], intervals[i + 1]);
  }

  for (const auto& i : intervals)
  {
    Trace("cdcac") << "Considering " << i.d_interval << std::endl;
    Trace("cdcac") << "-> " << i.d_lowerPolys << " / " << i.d_upperPolys
                   << " and " << i.d_mainPolys << " / " << i.d_downPolys
                   << std::endl;
    Trace("cdcac") << "-> " << i.d_origins << std::endl;
    for (const auto& p : i.d_downPolys)
    {
      // Add all polynomial from lower levels.
      res.add(p);
    }
    for (const auto& p : i.d_mainPolys)
    {
      Trace("cdcac::projection")
          << "Discriminant of " << p << " -> " << discriminant(p) << std::endl;
      // Add all discriminants
      res.add(discriminant(p));

      // Add pairwise resultants
      for (const auto& q : i.d_mainPolys)
      {
        // avoid symmetric duplicates
        if (p >= q) continue;
        res.add(resultant(p, q));
      }

      for (const auto& q : requiredCoefficients(p))
      {
        // Add all required coefficients
        Trace("cdcac::projection")
            << "Coeff of " << p << " -> " << q << std::endl;
        res.add(q);
      }
      for (const auto& q : i.d_lowerPolys)
      {
        if (p == q) continue;
        // Check whether p(s \times a) = 0 for some a <= l
        if (!hasRootBelow(q, get_lower(i.d_interval))) continue;
        Trace("cdcac::projection") << "Resultant of " << p << " and " << q
                                   << " -> " << resultant(p, q) << std::endl;
        res.add(resultant(p, q));
      }
      for (const auto& q : i.d_upperPolys)
      {
        if (p == q) continue;
        // Check whether p(s \times a) = 0 for some a >= u
        if (!hasRootAbove(q, get_upper(i.d_interval))) continue;
        Trace("cdcac::projection") << "Resultant of " << p << " and " << q
                                   << " -> " << resultant(p, q) << std::endl;
        res.add(resultant(p, q));
      }
    }
  }

  for (std::size_t i = 0, n = intervals.size(); i < n - 1; ++i)
  {
    // Add resultants of consecutive intervals.
    for (const auto& p : intervals[i].d_upperPolys)
    {
      for (const auto& q : intervals[i + 1].d_lowerPolys)
      {
        Trace("cdcac::projection") << "Resultant of " << p << " and " << q
                                   << " -> " << resultant(p, q) << std::endl;
        res.add(resultant(p, q));
      }
    }
  }

  res.reduce();
  res.makeFinestSquareFreeBasis();

  return res;
}

CACInterval CDCAC::intervalFromCharacterization(
    const PolyVector& characterization,
    std::size_t cur_variable,
    const poly::Value& sample)
{
  PolyVector l;
  PolyVector u;
  PolyVector m;
  PolyVector d;

  for (const auto& p : characterization)
  {
    // Add polynomials to main
    m.add(p);
  }
  // Push lower-dimensional polys to down
  m.pushDownPolys(d, d_variableOrdering[cur_variable]);

  // Collect -oo, all roots, oo

  LazardEvaluation le(statisticsRegistry());
  prepareRootIsolation(le, cur_variable);
  std::vector<poly::Value> roots;
  roots.emplace_back(poly::Value::minus_infty());
  for (const auto& p : m)
  {
    Trace("cdcac") << "Isolating real roots of " << p << " over "
                   << d_assignment << std::endl;

    auto tmp = isolateRealRoots(le, p);
    roots.insert(roots.end(), tmp.begin(), tmp.end());
  }
  roots.emplace_back(poly::Value::plus_infty());
  std::sort(roots.begin(), roots.end());

  // Now find the interval bounds
  poly::Value lower;
  poly::Value upper;
  for (std::size_t i = 0, n = roots.size(); i < n; ++i)
  {
    if (sample < roots[i])
    {
      lower = roots[i - 1];
      upper = roots[i];
      break;
    }
    if (roots[i] == sample)
    {
      lower = sample;
      upper = sample;
      break;
    }
  }
  Assert(!is_none(lower) && !is_none(upper));

  if (!is_minus_infinity(lower))
  {
    // Identify polynomials that have a root at the lower bound
    d_assignment.set(d_variableOrdering[cur_variable], lower);
    for (const auto& p : m)
    {
      Trace("cdcac") << "Evaluating " << p << " = 0 over " << d_assignment
                     << std::endl;
      if (evaluate_constraint(p, d_assignment, poly::SignCondition::EQ))
      {
        l.add(p, true);
      }
    }
    d_assignment.unset(d_variableOrdering[cur_variable]);
  }
  if (!is_plus_infinity(upper))
  {
    // Identify polynomials that have a root at the upper bound
    d_assignment.set(d_variableOrdering[cur_variable], upper);
    for (const auto& p : m)
    {
      Trace("cdcac") << "Evaluating " << p << " = 0 over " << d_assignment
                     << std::endl;
      if (evaluate_constraint(p, d_assignment, poly::SignCondition::EQ))
      {
        u.add(p, true);
      }
    }
    d_assignment.unset(d_variableOrdering[cur_variable]);
  }

  if (lower == upper)
  {
    // construct a point interval
    return CACInterval{d_nextIntervalId++,
                       poly::Interval(lower, false, upper, false),
                       l,
                       u,
                       m,
                       d,
                       {}};
  }
  else
  {
    // construct an open interval
    Assert(lower < upper);
    return CACInterval{d_nextIntervalId++,
                       poly::Interval(lower, true, upper, true),
                       l,
                       u,
                       m,
                       d,
                       {}};
  }
}

std::vector<CACInterval> CDCAC::getUnsatCoverImpl(std::size_t curVariable,
                                                  bool returnFirstInterval)
{
  d_env.getResourceManager()->spendResource(Resource::ArithNlCoveringStep);
  Trace("cdcac") << "Looking for unsat cover for "
                 << d_variableOrdering[curVariable] << std::endl;
  std::vector<CACInterval> intervals = getUnsatIntervals(curVariable);

  if (TraceIsOn("cdcac"))
  {
    Trace("cdcac") << "Unsat intervals for " << d_variableOrdering[curVariable]
                   << ":" << std::endl;
    for (const auto& i : intervals)
    {
      Trace("cdcac") << "-> " << i.d_interval << " from " << i.d_origins
                     << std::endl;
    }
  }
  poly::Value sample;

  while (sampleOutsideWithInitial(intervals, sample, curVariable))
  {
    if (!checkIntegrality(curVariable, sample))
    {
      // the variable is integral, but the sample is not.
      Trace("cdcac") << "Used " << sample << " for integer variable "
                     << d_variableOrdering[curVariable] << std::endl;
      auto newInterval = buildIntegralityInterval(curVariable, sample);
      Trace("cdcac") << "Adding integrality interval " << newInterval.d_interval
                     << std::endl;
      intervals.emplace_back(newInterval);
      pruneRedundantIntervals(intervals);
      continue;
    }
    d_assignment.set(d_variableOrdering[curVariable], sample);
    Trace("cdcac") << "Sample: " << d_assignment << std::endl;
    if (curVariable == d_variableOrdering.size() - 1)
    {
      // We have a full assignment. SAT!
      Trace("cdcac") << "Found full assignment: " << d_assignment << std::endl;
      return {};
    }
    if (isProofEnabled())
    {
      d_proof->startScope();
      d_proof->startRecursive();
    }
    // Recurse to next variable
    auto cov = getUnsatCoverImpl(curVariable + 1);
    if (cov.empty())
    {
      // Found SAT!
      Trace("cdcac") << "SAT!" << std::endl;
      return {};
    }
    Trace("cdcac") << "Refuting Sample: " << d_assignment << std::endl;
    auto characterization = constructCharacterization(cov);
    Trace("cdcac") << "Characterization: " << characterization << std::endl;

    d_assignment.unset(d_variableOrdering[curVariable]);

    Trace("cdcac") << "Building interval..." << std::endl;
    auto newInterval =
        intervalFromCharacterization(characterization, curVariable, sample);
    Trace("cdcac") << "New interval: " << newInterval.d_interval << std::endl;
    newInterval.d_origins = collectConstraints(cov);
    intervals.emplace_back(newInterval);
    if (isProofEnabled())
    {
      d_proof->endRecursive(newInterval.d_id);
      auto cell = d_proof->constructCell(
          d_constraints.varMapper()(d_variableOrdering[curVariable]),
          newInterval,
          d_assignment,
          sample,
          d_constraints.varMapper());
      d_proof->endScope(cell);
    }

    if (returnFirstInterval)
    {
      return intervals;
    }

    Trace("cdcac") << "Added " << intervals.back().d_interval << std::endl;
    Trace("cdcac") << "\tlower:   " << intervals.back().d_lowerPolys
                   << std::endl;
    Trace("cdcac") << "\tupper:   " << intervals.back().d_upperPolys
                   << std::endl;
    Trace("cdcac") << "\tmain:    " << intervals.back().d_mainPolys
                   << std::endl;
    Trace("cdcac") << "\tdown:    " << intervals.back().d_downPolys
                   << std::endl;
    Trace("cdcac") << "\torigins: " << intervals.back().d_origins << std::endl;

    // Remove redundant intervals
    pruneRedundantIntervals(intervals);
  }

  if (TraceIsOn("cdcac"))
  {
    Trace("cdcac") << "Returning intervals for "
                   << d_variableOrdering[curVariable] << ":" << std::endl;
    for (const auto& i : intervals)
    {
      Trace("cdcac") << "-> " << i.d_interval << std::endl;
    }
  }
  return intervals;
}

std::vector<CACInterval> CDCAC::getUnsatCover(bool returnFirstInterval)
{
  if (isProofEnabled())
  {
    d_proof->startRecursive();
  }
  auto res = getUnsatCoverImpl(0, returnFirstInterval);
  if (isProofEnabled())
  {
    d_proof->endRecursive(0);
  }
  return res;
}

void CDCAC::startNewProof()
{
  if (isProofEnabled())
  {
    d_proof->startNewProof();
  }
}

ProofGenerator* CDCAC::closeProof(const std::vector<Node>& assertions)
{
  if (isProofEnabled())
  {
    d_proof->endScope(assertions);
    return d_proof->getProofGenerator();
  }
  return nullptr;
}

bool CDCAC::checkIntegrality(std::size_t cur_variable, const poly::Value& value)
{
  Node var = d_constraints.varMapper()(d_variableOrdering[cur_variable]);
  if (var.getType() != NodeManager::currentNM()->integerType())
  {
    // variable is not integral
    return true;
  }
  return poly::represents_integer(value);
}

CACInterval CDCAC::buildIntegralityInterval(std::size_t cur_variable,
                                            const poly::Value& value)
{
  poly::Variable var = d_variableOrdering[cur_variable];
  poly::Integer below = poly::floor(value);
  poly::Integer above = poly::ceil(value);
  // construct var \in (below, above)
  return CACInterval{d_nextIntervalId++,
                     poly::Interval(below, above),
                     {var - below},
                     {var - above},
                     {var - below, var - above},
                     {},
                     {}};
}

bool CDCAC::hasRootAbove(const poly::Polynomial& p,
                         const poly::Value& val) const
{
  auto roots = poly::isolate_real_roots(p, d_assignment);
  return std::any_of(roots.begin(), roots.end(), [&val](const poly::Value& r) {
    return r >= val;
  });
}

bool CDCAC::hasRootBelow(const poly::Polynomial& p,
                         const poly::Value& val) const
{
  auto roots = poly::isolate_real_roots(p, d_assignment);
  return std::any_of(roots.begin(), roots.end(), [&val](const poly::Value& r) {
    return r <= val;
  });
}

void CDCAC::pruneRedundantIntervals(std::vector<CACInterval>& intervals)
{
  cleanIntervals(intervals);
  if (options().arith.nlCovPrune)
  {
    if (TraceIsOn("cdcac"))
    {
      auto copy = intervals;
      removeRedundantIntervals(intervals);
      if (copy.size() != intervals.size())
      {
        Trace("cdcac") << "Before pruning:";
        for (const auto& i : copy) Trace("cdcac") << " " << i.d_interval;
        Trace("cdcac") << std::endl;
        Trace("cdcac") << "After pruning: ";
        for (const auto& i : intervals) Trace("cdcac") << " " << i.d_interval;
        Trace("cdcac") << std::endl;
      }
    }
    else
    {
      removeRedundantIntervals(intervals);
    }
  }
  if (isProofEnabled())
  {
    d_proof->pruneChildren([&intervals](std::size_t id) {
      if (id == 0) return false;
      return std::find_if(intervals.begin(),
                          intervals.end(),
                          [id](const CACInterval& i) { return i.d_id == id; })
             == intervals.end();
    });
  }
}

void CDCAC::prepareRootIsolation(LazardEvaluation& le,
                                 size_t cur_variable) const
{
  if (options().arith.nlCovLifting == options::nlCovLiftingMode::LAZARD)
  {
    for (size_t vid = 0; vid < cur_variable; ++vid)
    {
      const auto& val = d_assignment.get(d_variableOrdering[vid]);
      le.add(d_variableOrdering[vid], val);
    }
    le.addFreeVariable(d_variableOrdering[cur_variable]);
  }
}

std::vector<poly::Value> CDCAC::isolateRealRoots(
    LazardEvaluation& le, const poly::Polynomial& p) const
{
  if (options().arith.nlCovLifting == options::nlCovLiftingMode::LAZARD)
  {
    return le.isolateRealRoots(p);
  }
  return poly::isolate_real_roots(p, d_assignment);
}

}  // namespace coverings
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif
