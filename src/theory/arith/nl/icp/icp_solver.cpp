/*********************                                                        */
/*! \file icp_solver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implements a ICP-based solver for nonlinear arithmetic.
 **/

#include "theory/arith/nl/icp/icp_solver.h"

#ifdef CVC4_POLY_IMP

#include <iostream>

#include "base/check.h"
#include "base/output.h"
#include "expr/node_algorithm.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/nl/poly_conversion.h"
#include "theory/arith/normal_form.h"
#include "theory/rewriter.h"
#include "util/poly_util.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {
namespace icp {

namespace {
/** A simple wrapper to nicely print an interval assignment. */
struct IAWrapper
{
  const poly::IntervalAssignment& ia;
  const VariableMapper& vm;
};
inline std::ostream& operator<<(std::ostream& os, const IAWrapper& iaw)
{
  os << "{ ";
  bool first = true;
  for (const auto& v : iaw.vm.mVarpolyCVC)
  {
    if (iaw.ia.has(v.first))
    {
      if (first)
      {
        first = false;
      }
      else
      {
        os << ", ";
      }
      os << v.first << " -> " << iaw.ia.get(v.first);
    }
  }
  return os << " }";
}
}  // namespace

std::vector<Node> ICPSolver::collectVariables(const Node& n) const
{
  std::unordered_set<TNode, TNodeHashFunction> tmp;
  expr::getVariables(n, tmp);
  std::vector<Node> res;
  for (const auto& t : tmp)
  {
    res.emplace_back(t);
  }
  return res;
}

std::vector<Candidate> ICPSolver::constructCandidates(const Node& n)
{
  auto comp = Comparison::parseNormalForm(n).decompose(false);
  Kind k = std::get<1>(comp);
  if (k == Kind::DISTINCT)
  {
    return {};
  }
  auto poly = std::get<0>(comp);

  std::vector<Candidate> result;
  std::unordered_set<TNode, TNodeHashFunction> vars;
  expr::getVariables(n, vars);
  for (const auto& v : vars)
  {
    Trace("nl-icp") << "\tChecking " << n << " for " << v << std::endl;

    std::map<Node, Node> msum;
    ArithMSum::getMonomialSum(poly.getNode(), msum);

    Node veq_c;
    Node val;

    int isolated = ArithMSum::isolate(v, msum, veq_c, val, k);
    if (isolated == 1)
    {
      poly::Variable lhs = d_mapper(v);
      poly::SignCondition rel;
      switch (k)
      {
        case Kind::LT: rel = poly::SignCondition::LT; break;
        case Kind::LEQ: rel = poly::SignCondition::LE; break;
        case Kind::EQUAL: rel = poly::SignCondition::EQ; break;
        case Kind::DISTINCT: rel = poly::SignCondition::NE; break;
        case Kind::GT: rel = poly::SignCondition::GT; break;
        case Kind::GEQ: rel = poly::SignCondition::GE; break;
        default: Assert(false) << "Unexpected kind: " << k;
      }
      poly::Rational rhsmult;
      poly::Polynomial rhs = as_poly_polynomial(val, d_mapper, rhsmult);
      rhsmult = poly::Rational(1) / rhsmult;
      // only correct up to a constant (denominator is thrown away!)
      // std::cout << "rhs = " << rhs << std::endl;
      if (!veq_c.isNull())
      {
        rhsmult = poly_utils::toRational(veq_c.getConst<Rational>());
      }
      Candidate res{lhs, rel, rhs, rhsmult, n, collectVariables(val)};
      Trace("nl-icp") << "\tAdded " << res << " from " << n << std::endl;
      result.emplace_back(res);
    }
    else if (isolated == -1)
    {
      poly::Variable lhs = d_mapper(v);
      poly::SignCondition rel;
      switch (k)
      {
        case Kind::LT: rel = poly::SignCondition::GT; break;
        case Kind::LEQ: rel = poly::SignCondition::GE; break;
        case Kind::EQUAL: rel = poly::SignCondition::EQ; break;
        case Kind::DISTINCT: rel = poly::SignCondition::NE; break;
        case Kind::GT: rel = poly::SignCondition::LT; break;
        case Kind::GEQ: rel = poly::SignCondition::LE; break;
        default: Assert(false) << "Unexpected kind: " << k;
      }
      poly::Rational rhsmult;
      poly::Polynomial rhs = as_poly_polynomial(val, d_mapper, rhsmult);
      rhsmult = poly::Rational(1) / rhsmult;
      if (!veq_c.isNull())
      {
        rhsmult = poly_utils::toRational(veq_c.getConst<Rational>());
      }
      Candidate res{lhs, rel, rhs, rhsmult, n, collectVariables(val)};
      Trace("nl-icp") << "\tAdded " << res << " from " << n << std::endl;
      result.emplace_back(res);
    }
  }
  return result;
}

void ICPSolver::addCandidate(const Node& n)
{
  auto it = d_candidateCache.find(n);
  if (it != d_candidateCache.end())
  {
    for (const auto& c : it->second)
    {
      d_state.d_candidates.emplace_back(c);
    }
  }
  else
  {
    auto cands = constructCandidates(n);
    d_candidateCache.emplace(n, cands);
    for (const auto& c : cands)
    {
      d_state.d_candidates.emplace_back(c);
      Trace("nl-icp") << "Bumping budget because of the new candidate"
                      << std::endl;
      d_budget += d_budgetIncrement;
    }
  }
}

void ICPSolver::initOrigins()
{
  for (const auto& vars : d_mapper.mVarCVCpoly)
  {
    auto& i = d_state.d_bounds.get(vars.first);
    Trace("nl-icp") << "Adding initial " << vars.first << " -> " << i
                    << std::endl;
    if (!i.lower_origin.isNull())
    {
      Trace("nl-icp") << "\tAdding lower " << i.lower_origin << std::endl;
      d_state.d_origins.add(vars.first, i.lower_origin, {});
    }
    if (!i.upper_origin.isNull())
    {
      Trace("nl-icp") << "\tAdding upper " << i.upper_origin << std::endl;
      d_state.d_origins.add(vars.first, i.upper_origin, {});
    }
  }
}

PropagationResult ICPSolver::doPropagationRound()
{
  if (d_budget <= 0)
  {
    Trace("nl-icp") << "ICP budget exceeded" << std::endl;
    return PropagationResult::NOT_CHANGED;
  }
  d_state.d_conflict = Node();
  Trace("nl-icp") << "Starting propagation with "
                  << IAWrapper{d_state.d_assignment, d_mapper} << std::endl;
  Trace("nl-icp") << "Current budget: " << d_budget << std::endl;
  PropagationResult res = PropagationResult::NOT_CHANGED;
  for (const auto& c : d_state.d_candidates)
  {
    --d_budget;
    PropagationResult cres = c.propagate(d_state.d_assignment, 100);
    switch (cres)
    {
      case PropagationResult::NOT_CHANGED: break;
      case PropagationResult::CONTRACTED:
      case PropagationResult::CONTRACTED_STRONGLY:
        d_state.d_origins.add(d_mapper(c.lhs), c.origin, c.rhsVariables);
        res = PropagationResult::CONTRACTED;
        break;
      case PropagationResult::CONTRACTED_WITHOUT_CURRENT:
      case PropagationResult::CONTRACTED_STRONGLY_WITHOUT_CURRENT:
        d_state.d_origins.add(d_mapper(c.lhs), c.origin, c.rhsVariables, false);
        res = PropagationResult::CONTRACTED;
        break;
      case PropagationResult::CONFLICT:
        d_state.d_origins.add(d_mapper(c.lhs), c.origin, c.rhsVariables);
        d_state.d_conflict = d_state.d_origins.getOrigins(d_mapper(c.lhs));
        return PropagationResult::CONFLICT;
    }
    switch (cres)
    {
      case PropagationResult::CONTRACTED_STRONGLY:
      case PropagationResult::CONTRACTED_STRONGLY_WITHOUT_CURRENT:
        Trace("nl-icp") << "Bumping budget because of a strong contraction"
                        << std::endl;
        d_budget += d_budgetIncrement;
        break;
      default: break;
    }
  }
  return res;
}

std::vector<Node> ICPSolver::generateLemmas() const
{
  auto nm = NodeManager::currentNM();
  std::vector<Node> lemmas;

  for (const auto& vars : d_mapper.mVarCVCpoly)
  {
    if (!d_state.d_assignment.has(vars.second)) continue;
    Node v = vars.first;
    poly::Interval i = d_state.d_assignment.get(vars.second);
    if (!is_minus_infinity(get_lower(i)))
    {
      Kind rel = get_lower_open(i) ? Kind::GT : Kind::GEQ;
      Node c = nm->mkNode(rel, v, value_to_node(get_lower(i), v));
      Node premise = d_state.d_origins.getOrigins(v);
      Trace("nl-icp") << premise << " => " << c << std::endl;
      Node lemma = Rewriter::rewrite(nm->mkNode(Kind::IMPLIES, premise, c));
      if (lemma.isConst())
      {
        Assert(lemma == nm->mkConst<bool>(true));
      }
      else
      {
        Trace("nl-icp") << "Adding lemma " << lemma << std::endl;
        lemmas.emplace_back(lemma);
      }
    }
    if (!is_plus_infinity(get_upper(i)))
    {
      Kind rel = get_upper_open(i) ? Kind::LT : Kind::LEQ;
      Node c = nm->mkNode(rel, v, value_to_node(get_upper(i), v));
      Node premise = d_state.d_origins.getOrigins(v);
      Trace("nl-icp") << premise << " => " << c << std::endl;
      Node lemma = Rewriter::rewrite(nm->mkNode(Kind::IMPLIES, premise, c));
      if (lemma.isConst())
      {
        Assert(lemma == nm->mkConst<bool>(true));
      }
      else
      {
        Trace("nl-icp") << "Adding lemma " << lemma << std::endl;
        lemmas.emplace_back(lemma);
      }
    }
  }
  return lemmas;
}

void ICPSolver::reset(const std::vector<Node>& assertions)
{
  d_state.reset();
  for (const auto& n : assertions)
  {
    Node tmp = Rewriter::rewrite(n);
    Trace("nl-icp") << "Adding " << tmp << std::endl;
    if (tmp.getKind() != Kind::CONST_BOOLEAN)
    {
      if (!d_state.d_bounds.add(tmp))
      {
        addCandidate(tmp);
      }
    }
  }
}

void ICPSolver::check()
{
  initOrigins();
  d_state.d_assignment = d_state.d_bounds.get();
  bool did_progress = false;
  bool progress = false;
  do
  {
    switch (doPropagationRound())
    {
      case icp::PropagationResult::NOT_CHANGED: progress = false; break;
      case icp::PropagationResult::CONTRACTED:
      case icp::PropagationResult::CONTRACTED_STRONGLY:
      case icp::PropagationResult::CONTRACTED_WITHOUT_CURRENT:
      case icp::PropagationResult::CONTRACTED_STRONGLY_WITHOUT_CURRENT:
        did_progress = true;
        progress = true;
        break;
      case icp::PropagationResult::CONFLICT:
        Trace("nl-icp") << "Found a conflict: " << d_state.d_conflict
                        << std::endl;

        d_im.addConflict(d_state.d_conflict, InferenceId::NL_ICP_CONFLICT);
        did_progress = true;
        progress = false;
        break;
    }
  } while (progress);
  if (did_progress)
  {
    for (const auto& l : generateLemmas())
    {
      d_im.addPendingArithLemma(l, InferenceId::NL_ICP_PROPAGATION);
    }
  }
}

}  // namespace icp
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif