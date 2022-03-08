/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for converting to and from LibPoly objects.
 */

#include "poly_conversion.h"

#ifdef CVC5_POLY_IMP

#include "expr/node.h"
#include "expr/node_manager_attributes.h"
#include "theory/arith/bound_inference.h"
#include "util/poly_util.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace arith {
namespace nl {

poly::Variable VariableMapper::operator()(const cvc5::Node& n)
{
  auto it = mVarCVCpoly.find(n);
  if (it == mVarCVCpoly.end())
  {
    std::string name;
    if (n.isVar())
    {
      if (!n.getAttribute(expr::VarNameAttr(), name))
      {
        Trace("poly::conversion")
            << "Variable " << n << " has no name, using ID instead."
            << std::endl;
        name = "v_" + std::to_string(n.getId());
      }
    }
    else
    {
      name = "v_" + std::to_string(n.getId());
    }
    it = mVarCVCpoly.emplace(n, poly::Variable(name.c_str())).first;
    mVarpolyCVC.emplace(it->second, n);
  }
  return it->second;
}

cvc5::Node VariableMapper::operator()(const poly::Variable& n)
{
  auto it = mVarpolyCVC.find(n);
  Assert(it != mVarpolyCVC.end())
      << "Expect variable " << n << " to be added already.";
  return it->second;
}

cvc5::Node as_cvc_upolynomial(const poly::UPolynomial& p, const cvc5::Node& var)
{
  Trace("poly::conversion")
      << "Converting " << p << " over " << var << std::endl;

  std::vector<poly::Integer> coeffs = coefficients(p);

  auto* nm = NodeManager::currentNM();

  Node res = nm->mkConst(CONST_RATIONAL, Rational(0));
  Node monomial = nm->mkConst(CONST_RATIONAL, Rational(1));
  for (std::size_t i = 0, n = coeffs.size(); i < n; ++i)
  {
    if (!is_zero(coeffs[i]))
    {
      Node coeff =
          nm->mkConst(CONST_RATIONAL, poly_utils::toRational(coeffs[i]));
      Node term = nm->mkNode(Kind::MULT, coeff, monomial);
      res = nm->mkNode(Kind::ADD, res, term);
    }
    monomial = nm->mkNode(Kind::NONLINEAR_MULT, monomial, var);
  }
  Trace("poly::conversion") << "-> " << res << std::endl;
  return res;
}

poly::UPolynomial as_poly_upolynomial_impl(const cvc5::Node& n,
                                           poly::Integer& denominator,
                                           const cvc5::Node& var)
{
  denominator = poly::Integer(1);
  if (n.isVar())
  {
    Assert(n == var) << "Unexpected variable: should be " << var << " but is "
                     << n;
    return poly::UPolynomial({0, 1});
  }
  switch (n.getKind())
  {
    case Kind::CONST_RATIONAL:
    {
      Rational r = n.getConst<Rational>();
      denominator = poly_utils::toInteger(r.getDenominator());
      return poly::UPolynomial(poly_utils::toInteger(r.getNumerator()));
    }
    case Kind::ADD:
    {
      poly::UPolynomial res;
      poly::Integer denom;
      for (const auto& child : n)
      {
        poly::UPolynomial tmp = as_poly_upolynomial_impl(child, denom, var);
        /** Normalize denominators
         */
        poly::Integer g = gcd(denom, denominator);
        res = res * (denom / g) + tmp * (denominator / g);
        denominator *= (denom / g);
      }
      return res;
    }
    case Kind::MULT:
    case Kind::NONLINEAR_MULT:
    {
      poly::UPolynomial res(denominator);
      poly::Integer denom;
      for (const auto& child : n)
      {
        res = res * as_poly_upolynomial_impl(child, denom, var);
        denominator *= denom;
      }
      return res;
    }
    default:
      Assert(false) << "Unhandled node " << n << " with kind " << n.getKind()
                << std::endl;
  }
  return poly::UPolynomial();
}

poly::UPolynomial as_poly_upolynomial(const cvc5::Node& n,
                                      const cvc5::Node& var)
{
  poly::Integer denom;
  return as_poly_upolynomial_impl(n, denom, var);
}

poly::Polynomial as_poly_polynomial_impl(const cvc5::Node& n,
                                         poly::Integer& denominator,
                                         VariableMapper& vm)
{
  denominator = poly::Integer(1);
  if (n.isVar())
  {
    return poly::Polynomial(vm(n));
  }
  switch (n.getKind())
  {
    case Kind::CONST_RATIONAL:
    {
      Rational r = n.getConst<Rational>();
      denominator = poly_utils::toInteger(r.getDenominator());
      return poly::Polynomial(poly_utils::toInteger(r.getNumerator()));
    }
    case Kind::ADD:
    {
      poly::Polynomial res;
      poly::Integer denom;
      for (const auto& child : n)
      {
        poly::Polynomial tmp = as_poly_polynomial_impl(child, denom, vm);
        /** Normalize denominators
         */
        poly::Integer g = gcd(denom, denominator);
        res = res * (denom / g) + tmp * (denominator / g);
        denominator *= (denom / g);
      }
      return res;
    }
    case Kind::MULT:
    case Kind::NONLINEAR_MULT:
    {
      poly::Polynomial res(denominator);
      poly::Integer denom;
      for (const auto& child : n)
      {
        res *= as_poly_polynomial_impl(child, denom, vm);
        denominator *= denom;
      }
      return res;
    }
    default: return poly::Polynomial(vm(n));
  }
  return poly::Polynomial();
}
poly::Polynomial as_poly_polynomial(const cvc5::Node& n, VariableMapper& vm)
{
  poly::Integer denom;
  return as_poly_polynomial_impl(n, denom, vm);
}
poly::Polynomial as_poly_polynomial(const cvc5::Node& n,
                                    VariableMapper& vm,
                                    poly::Rational& denominator)
{
  poly::Integer denom;
  auto res = as_poly_polynomial_impl(n, denom, vm);
  denominator = poly::Rational(denom);
  return res;
}

namespace {
/**
 * Utility class that collects the monomial terms (as nodes) from the polynomial
 * we are converting.
 */
struct CollectMonomialData
{
  CollectMonomialData(VariableMapper& v) : d_vm(v) {}

  /** Mapper from poly variables to cvc5 variables */
  VariableMapper& d_vm;
  /** Collections of the monomial terms */
  std::vector<Node> d_terms;
  /** Caches the current node manager */
  NodeManager* d_nm = NodeManager::currentNM();
};
/**
 * Callback for lp_polynomial_traverse. Assumes data is actually a
 * CollectMonomialData object and puts the polynomial into it.
 */
void collect_monomials(const lp_polynomial_context_t* ctx,
                       lp_monomial_t* m,
                       void* data)
{
  CollectMonomialData* d = static_cast<CollectMonomialData*>(data);
  // constant
  Node term = d->d_nm->mkConst<Rational>(
      CONST_RATIONAL, poly_utils::toRational(poly::Integer(&m->a)));
  for (std::size_t i = 0; i < m->n; ++i)
  {
    // variable exponent pair
    Node var = d->d_vm(m->p[i].x);
    if (m->p[i].d > 1)
    {
      Node exp = d->d_nm->mkConst<Rational>(CONST_RATIONAL, m->p[i].d);
      term = d->d_nm->mkNode(
          Kind::NONLINEAR_MULT, term, d->d_nm->mkNode(Kind::POW, var, exp));
    }
    else
    {
      term = d->d_nm->mkNode(Kind::NONLINEAR_MULT, term, var);
    }
  }
  d->d_terms.emplace_back(term);
}
}  // namespace

cvc5::Node as_cvc_polynomial(const poly::Polynomial& p, VariableMapper& vm)
{
  CollectMonomialData cmd(vm);
  // Do the actual conversion
  lp_polynomial_traverse(p.get_internal(), collect_monomials, &cmd);

  if (cmd.d_terms.empty())
  {
    return cmd.d_nm->mkConst<Rational>(CONST_RATIONAL, 0);
  }
  if (cmd.d_terms.size() == 1)
  {
    return cmd.d_terms.front();
  }
  return cmd.d_nm->mkNode(Kind::ADD, cmd.d_terms);
}

poly::SignCondition normalize_kind(cvc5::Kind kind,
                                   bool negated,
                                   poly::Polynomial& lhs)
{
  switch (kind)
  {
    case Kind::EQUAL:
    {
      return negated ? poly::SignCondition::NE : poly::SignCondition::EQ;
    }
    case Kind::LT:
    {
      if (negated)
      {
        lhs = -lhs;
        return poly::SignCondition::LE;
      }
      return poly::SignCondition::LT;
    }
    case Kind::LEQ:
    {
      if (negated)
      {
        lhs = -lhs;
        return poly::SignCondition::LT;
      }
      return poly::SignCondition::LE;
    }
    case Kind::GT:
    {
      if (negated)
      {
        return poly::SignCondition::LE;
      }
      lhs = -lhs;
      return poly::SignCondition::LT;
    }
    case Kind::GEQ:
    {
      if (negated)
      {
        return poly::SignCondition::LT;
      }
      lhs = -lhs;
      return poly::SignCondition::LE;
    }
    default:
      Assert(false) << "This function only deals with arithmetic relations.";
      return poly::SignCondition::EQ;
  }
}

std::pair<poly::Polynomial, poly::SignCondition> as_poly_constraint(
    Node n, VariableMapper& vm)
{
  bool negated = false;
  Node origin = n;
  if (n.getKind() == Kind::NOT)
  {
    Assert(n.getNumChildren() == 1)
        << "Expect negations to have a single child.";
    negated = true;
    n = *n.begin();
  }
  Assert((n.getKind() == Kind::EQUAL) || (n.getKind() == Kind::GT)
         || (n.getKind() == Kind::GEQ) || (n.getKind() == Kind::LT)
         || (n.getKind() == Kind::LEQ))
      << "Found a constraint with unsupported relation " << n.getKind();

  Assert(n.getNumChildren() == 2)
      << "Supported relations only have two children.";
  auto childit = n.begin();
  poly::Integer ldenom;
  poly::Polynomial left = as_poly_polynomial_impl(*childit++, ldenom, vm);
  poly::Integer rdenom;
  poly::Polynomial right = as_poly_polynomial_impl(*childit++, rdenom, vm);
  Assert(childit == n.end()) << "Screwed up iterator handling.";
  Assert(ldenom > poly::Integer(0) && rdenom > poly::Integer(0))
      << "Expected denominators to be always positive.";

  poly::Integer g = gcd(ldenom, rdenom);
  poly::Polynomial lhs = left * (rdenom / g) - right * (ldenom / g);
  poly::SignCondition sc = normalize_kind(n.getKind(), negated, lhs);
  return {lhs, sc};
}

Node ran_to_node(const RealAlgebraicNumber& ran, const Node& ran_variable)
{
  return ran_to_node(ran.getValue(), ran_variable);
}

Node ran_to_node(const poly::AlgebraicNumber& an, const Node& ran_variable)
{
  auto* nm = NodeManager::currentNM();

  const poly::DyadicInterval& di = get_isolating_interval(an);
  if (is_point(di))
  {
    return nm->mkConst(CONST_RATIONAL, poly_utils::toRational(get_point(di)));
  }
  Assert(di.get_internal()->a_open && di.get_internal()->b_open)
      << "We assume an open interval here.";

  Node poly = as_cvc_upolynomial(get_defining_polynomial(an), ran_variable);
  Node lower =
      nm->mkConst(CONST_RATIONAL, poly_utils::toRational(get_lower(di)));
  Node upper =
      nm->mkConst(CONST_RATIONAL, poly_utils::toRational(get_upper(di)));

  // Construct witness:
  return nm->mkNode(
      Kind::AND,
      // poly(var) == 0
      nm->mkNode(Kind::EQUAL, poly, nm->mkConst(CONST_RATIONAL, Rational(0))),
      // lower_bound < var
      nm->mkNode(Kind::LT, lower, ran_variable),
      // var < upper_bound
      nm->mkNode(Kind::LT, ran_variable, upper));
}

Node value_to_node(const poly::Value& v, const Node& ran_variable)
{
  Assert(!is_minus_infinity(v)) << "Can not convert minus infinity.";
  Assert(!is_none(v)) << "Can not convert none.";
  Assert(!is_plus_infinity(v)) << "Can not convert plus infinity.";

  auto* nm = NodeManager::currentNM();
  if (is_algebraic_number(v))
  {
    auto ran = as_algebraic_number(v);
    return nm->mkRealAlgebraicNumber(RealAlgebraicNumber(std::move(ran)));
  }
  if (is_dyadic_rational(v))
  {
    return nm->mkConst(CONST_RATIONAL,
                       poly_utils::toRational(as_dyadic_rational(v)));
  }
  if (is_integer(v))
  {
    return nm->mkConst(CONST_RATIONAL, poly_utils::toRational(as_integer(v)));
  }
  if (is_rational(v))
  {
    return nm->mkConst(CONST_RATIONAL, poly_utils::toRational(as_rational(v)));
  }
  Assert(false) << "All cases should be covered.";
  return nm->mkConst(CONST_RATIONAL, Rational(0));
}

Node lower_bound_as_node(const Node& var,
                         const poly::Value& lower,
                         bool open,
                         bool allowNonlinearLemma)
{
  auto* nm = NodeManager::currentNM();
  if (!poly::is_algebraic_number(lower))
  {
    return nm->mkNode(
        open ? Kind::LEQ : Kind::LT,
        var,
        nm->mkConst(CONST_RATIONAL, poly_utils::toRationalAbove(lower)));
  }
  if (poly::represents_rational(lower))
  {
    return nm->mkNode(
        open ? Kind::LEQ : Kind::LT,
        var,
        nm->mkConst(CONST_RATIONAL,
                    poly_utils::toRationalAbove(poly::get_rational(lower))));
  }
  if (!allowNonlinearLemma)
  {
    return Node();
  }

  const poly::AlgebraicNumber& alg = as_algebraic_number(lower);

  Node poly = as_cvc_upolynomial(get_defining_polynomial(alg), var);
  Rational l = poly_utils::toRational(
      poly::get_lower(poly::get_isolating_interval(alg)));
  Rational u = poly_utils::toRational(
      poly::get_upper(poly::get_isolating_interval(alg)));
  int sl = poly::sign_at(get_defining_polynomial(alg),
                         poly::get_lower(poly::get_isolating_interval(alg)));
#ifdef CVC5_ASSERTIONS
  int su = poly::sign_at(get_defining_polynomial(alg),
                         poly::get_upper(poly::get_isolating_interval(alg)));
  Assert(sl != 0 && su != 0 && sl != su);
#endif

  // open:  var <= l  or  (var < u  and  sgn(poly(var)) == sl)
  // !open: var <= l  or  (var < u  and  sgn(poly(var)) == sl/0)
  Kind relation;
  if (open)
  {
    relation = (sl < 0) ? Kind::LEQ : Kind::GEQ;
  }
  else
  {
    relation = (sl < 0) ? Kind::LT : Kind::GT;
  }
  return nm->mkNode(
      Kind::OR,
      nm->mkNode(Kind::LEQ, var, nm->mkConst(CONST_RATIONAL, l)),
      nm->mkNode(
          Kind::AND,
          nm->mkNode(Kind::LT, var, nm->mkConst(CONST_RATIONAL, u)),
          nm->mkNode(
              relation, poly, nm->mkConst(CONST_RATIONAL, Rational(0)))));
}

Node upper_bound_as_node(const Node& var,
                         const poly::Value& upper,
                         bool open,
                         bool allowNonlinearLemma)
{
  auto* nm = NodeManager::currentNM();
  if (!poly::is_algebraic_number(upper))
  {
    return nm->mkNode(
        open ? Kind::GEQ : Kind::GT,
        var,
        nm->mkConst(CONST_RATIONAL, poly_utils::toRationalAbove(upper)));
  }
  if (poly::represents_rational(upper))
  {
    return nm->mkNode(
        open ? Kind::GEQ : Kind::GT,
        var,
        nm->mkConst(CONST_RATIONAL,
                    poly_utils::toRationalAbove(poly::get_rational(upper))));
  }
  if (!allowNonlinearLemma)
  {
    return Node();
  }

  const poly::AlgebraicNumber& alg = as_algebraic_number(upper);

  Node poly = as_cvc_upolynomial(get_defining_polynomial(alg), var);
  Rational l = poly_utils::toRational(
      poly::get_lower(poly::get_isolating_interval(alg)));
  Rational u = poly_utils::toRational(
      poly::get_upper(poly::get_isolating_interval(alg)));
#ifdef CVC5_ASSERTIONS
  int sl = poly::sign_at(get_defining_polynomial(alg),
                         poly::get_lower(poly::get_isolating_interval(alg)));
#endif
  int su = poly::sign_at(get_defining_polynomial(alg),
                         poly::get_upper(poly::get_isolating_interval(alg)));
  Assert(sl != 0 && su != 0 && sl != su);

  // open:  var >= u  or  (var > l  and  sgn(poly(var)) == su)
  // !open: var >= u  or  (var > l  and  sgn(poly(var)) == su/0)
  Kind relation;
  if (open)
  {
    relation = (su < 0) ? Kind::LEQ : Kind::GEQ;
  }
  else
  {
    relation = (su < 0) ? Kind::LT : Kind::GT;
  }
  return nm->mkNode(
      Kind::OR,
      nm->mkNode(Kind::GEQ, var, nm->mkConst(CONST_RATIONAL, u)),
      nm->mkNode(
          Kind::AND,
          nm->mkNode(Kind::GT, var, nm->mkConst(CONST_RATIONAL, l)),
          nm->mkNode(
              relation, poly, nm->mkConst(CONST_RATIONAL, Rational(0)))));
}

Node excluding_interval_to_lemma(const Node& variable,
                                 const poly::Interval& interval,
                                 bool allowNonlinearLemma)
{
  auto* nm = NodeManager::currentNM();
  const auto& lv = poly::get_lower(interval);
  const auto& uv = poly::get_upper(interval);
  if (bitsize(lv) > 100 || bitsize(uv) > 100) return Node();
  bool li = poly::is_minus_infinity(lv);
  bool ui = poly::is_plus_infinity(uv);
  if (li && ui) return nm->mkConst(true);
  if (poly::is_point(interval))
  {
    if (is_algebraic_number(lv))
    {
      const poly::AlgebraicNumber& alg = as_algebraic_number(lv);
      if (poly::is_rational(alg))
      {
        Trace("nl-cov") << "Rational point interval: " << interval << std::endl;
        return nm->mkNode(
            Kind::DISTINCT,
            variable,
            nm->mkConst(
                CONST_RATIONAL,
                poly_utils::toRational(poly::to_rational_approximation(alg))));
      }
      Trace("nl-cov") << "Algebraic point interval: " << interval << std::endl;
      // p(x) != 0 or x <= lb or ub <= x
      if (allowNonlinearLemma)
      {
        Node poly = as_cvc_upolynomial(get_defining_polynomial(alg), variable);
        return nm->mkNode(
            Kind::OR,
            nm->mkNode(
                Kind::DISTINCT, poly, nm->mkConst(CONST_RATIONAL, Rational(0))),
            nm->mkNode(
                Kind::LT,
                variable,
                nm->mkConst(CONST_RATIONAL, poly_utils::toRationalBelow(lv))),
            nm->mkNode(
                Kind::GT,
                variable,
                nm->mkConst(CONST_RATIONAL, poly_utils::toRationalAbove(lv))));
      }
      return Node();
    }
    else
    {
      Trace("nl-cov") << "Rational point interval: " << interval << std::endl;
      return nm->mkNode(
          Kind::DISTINCT,
          variable,
          nm->mkConst(CONST_RATIONAL, poly_utils::toRationalBelow(lv)));
    }
  }
  if (li)
  {
    Trace("nl-cov") << "Only upper bound: " << interval << std::endl;
    return upper_bound_as_node(
        variable, uv, poly::get_upper_open(interval), allowNonlinearLemma);
  }
  if (ui)
  {
    Trace("nl-cov") << "Only lower bound: " << interval << std::endl;
    return lower_bound_as_node(
        variable, lv, poly::get_lower_open(interval), allowNonlinearLemma);
  }
  Trace("nl-cov") << "Proper interval: " << interval << std::endl;
  Node lb = lower_bound_as_node(
      variable, lv, poly::get_lower_open(interval), allowNonlinearLemma);
  Node ub = upper_bound_as_node(
      variable, uv, poly::get_upper_open(interval), allowNonlinearLemma);
  if (lb.isNull() || ub.isNull()) return Node();
  return nm->mkNode(Kind::OR, lb, ub);
}

std::optional<Rational> get_lower_bound(const Node& n)
{
  if (n.getNumChildren() != 2) return std::optional<Rational>();
  if (n.getKind() == Kind::LT)
  {
    if (!n[0].isConst()) return std::optional<Rational>();
    if (!n[1].isVar()) return std::optional<Rational>();
    return n[0].getConst<Rational>();
  }
  else if (n.getKind() == Kind::GT)
  {
    if (!n[0].isVar()) return std::optional<Rational>();
    if (!n[1].isConst()) return std::optional<Rational>();
    return n[1].getConst<Rational>();
  }
  return std::optional<Rational>();
}
std::optional<Rational> get_upper_bound(const Node& n)
{
  if (n.getNumChildren() != 2) return std::optional<Rational>();
  if (n.getKind() == Kind::LT)
  {
    if (!n[0].isVar()) return std::optional<Rational>();
    if (!n[1].isConst()) return std::optional<Rational>();
    return n[1].getConst<Rational>();
  }
  else if (n.getKind() == Kind::GT)
  {
    if (!n[0].isConst()) return std::optional<Rational>();
    if (!n[1].isVar()) return std::optional<Rational>();
    return n[0].getConst<Rational>();
  }
  return std::optional<Rational>();
}

/** Returns indices of appropriate parts of ran encoding.
 * Returns (poly equation ; lower bound ; upper bound)
 */
std::tuple<Node, Rational, Rational> detect_ran_encoding(const Node& n)
{
  Assert(n.getKind() == Kind::AND) << "Invalid node structure.";
  Assert(n.getNumChildren() == 3) << "Invalid node structure.";

  Node poly_eq;
  if (n[0].getKind() == Kind::EQUAL)
    poly_eq = n[0];
  else if (n[1].getKind() == Kind::EQUAL)
    poly_eq = n[1];
  else if (n[2].getKind() == Kind::EQUAL)
    poly_eq = n[2];
  else
    Assert(false) << "Could not identify polynomial equation.";

  Node poly;
  Assert(poly_eq.getNumChildren() == 2) << "Invalid polynomial equation.";
  if (poly_eq[0].isConst())
  {
    Assert(poly_eq[0].getConst<Rational>() == Rational(0))
        << "Invalid polynomial equation.";
    poly = poly_eq[1];
  }
  else if (poly_eq[1].isConst())
  {
    Assert(poly_eq[1].getConst<Rational>() == Rational(0))
        << "Invalid polynomial equation.";
    poly = poly_eq[0];
  }
  else
  {
    Assert(false) << "Invalid polynomial equation.";
  }

  std::optional<Rational> lower = get_lower_bound(n[0]);
  if (!lower) lower = get_lower_bound(n[1]);
  if (!lower) lower = get_lower_bound(n[2]);
  Assert(lower) << "Could not identify lower bound.";

  std::optional<Rational> upper = get_upper_bound(n[0]);
  if (!upper) upper = get_upper_bound(n[1]);
  if (!upper) upper = get_upper_bound(n[2]);
  Assert(upper) << "Could not identify upper bound.";

  return std::tuple<Node, Rational, Rational>(
      poly, lower.value(), upper.value());
}

poly::AlgebraicNumber node_to_poly_ran(const Node& n, const Node& ran_variable)
{
  // Identify poly, lower and upper
  auto encoding = detect_ran_encoding(n);
  // Construct polynomial
  poly::UPolynomial pol =
      as_poly_upolynomial(std::get<0>(encoding), ran_variable);
  // Construct algebraic number
  return poly_utils::toPolyRanWithRefinement(
      std::move(pol), std::get<1>(encoding), std::get<2>(encoding));
}
RealAlgebraicNumber node_to_ran(const Node& n, const Node& ran_variable)
{
  return RealAlgebraicNumber(node_to_poly_ran(n, ran_variable));
}

poly::Value node_to_value(const Node& n, const Node& ran_variable)
{
  if (n.isConst())
  {
    return poly_utils::toRational(n.getConst<Rational>());
  }
  return node_to_poly_ran(n, ran_variable);
}

/** Bitsize of a dyadic rational. */
std::size_t bitsize(const poly::DyadicRational& v)
{
  return bit_size(numerator(v)) + bit_size(denominator(v));
}
/** Bitsize of an integer. */
std::size_t bitsize(const poly::Integer& v) { return bit_size(v); }
/** Bitsize of a rational. */
std::size_t bitsize(const poly::Rational& v)
{
  return bit_size(numerator(v)) + bit_size(denominator(v));
}
/** Bitsize of a univariate polynomial. */
std::size_t bitsize(const poly::UPolynomial& v)
{
  std::size_t sum = 0;
  for (const auto& c : coefficients(v))
  {
    sum += bitsize(c);
  }
  return sum;
}
/** Bitsize of an algebraic number. */
std::size_t bitsize(const poly::AlgebraicNumber& v)
{
  if (is_rational(v))
  {
    return bitsize(to_rational_approximation(v));
  }
  return bitsize(get_lower_bound(v)) + bitsize(get_upper_bound(v))
         + bitsize(get_defining_polynomial(v));
}

std::size_t bitsize(const poly::Value& v)
{
  if (is_algebraic_number(v))
  {
    return bitsize(as_algebraic_number(v));
  }
  else if (is_dyadic_rational(v))
  {
    return bitsize(as_dyadic_rational(v));
  }
  else if (is_integer(v))
  {
    return bitsize(as_integer(v));
  }
  else if (is_minus_infinity(v))
  {
    return 1;
  }
  else if (is_none(v))
  {
    return 0;
  }
  else if (is_plus_infinity(v))
  {
    return 1;
  }
  else if (is_rational(v))
  {
    return bitsize(as_rational(v));
  }
  Assert(false);
  return 0;
}

poly::IntervalAssignment getBounds(VariableMapper& vm, const BoundInference& bi)
{
  poly::IntervalAssignment res;
  for (const auto& vb : bi.get())
  {
    poly::Variable v = vm(vb.first);
    poly::Value l = vb.second.lower_value.isNull()
                        ? poly::Value::minus_infty()
                        : node_to_value(vb.second.lower_value, vb.first);
    poly::Value u = vb.second.upper_value.isNull()
                        ? poly::Value::plus_infty()
                        : node_to_value(vb.second.upper_value, vb.first);
    poly::Interval i(l, vb.second.lower_strict, u, vb.second.upper_strict);
    res.set(v, i);
  }
  return res;
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif
