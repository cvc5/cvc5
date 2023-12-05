/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * parsing structured field terms
 *
 * NB: many functions in this file return an empty std::optional if parsing
 * fails.
 */

#include "theory/ff/parse.h"

// external includes

// std includes
#include <numeric>
#include <optional>
#include <unordered_map>
#include <unordered_set>

// internal includes
#include "theory/ff/util.h"
#include "theory/theory.h"

namespace cvc5::internal {
namespace theory {
namespace ff {
namespace parse {

// fwd declarations for Spectrum
namespace {

/**
 * Characterization of a univariate, degree <= 2 polynomial.
 * The members uniquely determine such a polynomial, up to its leading
 * coefficient.
 *
 * This is a helper class for parsing terms that constrain a variable to be: 0,
 * 1, or both.
 */
struct Spectrum
{
  /** the variable; ignore if degree is 0 */
  Node var;
  /** the degree in {0, 1, 2} */
  uint8_t degree;
  /** value at 0 */
  FiniteFieldValue val0;
  /** value at 1 */
  FiniteFieldValue val1;
};

using SpectrumOpt = std::optional<Spectrum>;

/**
 * Attempt to compute a Spectrum for the polynomial defined by t.
 *
 * @param t a field term
 * @param depth how deep to search in term before giving up; reducing the depth
 *              reduces the runtime of this function, but increases the number
 *              of terms for which this function returns an empty optional.
 *              depth 5 is enough to parse all the patterns I've seen for
 *              bit constraints and similar.
 * @return none if t is too deep or mulitvariate or has degreee > 2; otherwise,
 * a Spectrum.
 */
SpectrumOpt spectrum(const Node& t, uint8_t depth = 5);

}  // namespace

bool zeroConstraint(const Node& fact)
{
  SpectrumOpt r = spectrum(fact);
  return r.has_value() && r->degree == 1 && r->val0.getValue() == 0;
}

bool oneConstraint(const Node& fact)
{
  SpectrumOpt r = spectrum(fact);
  return r.has_value() && r->degree == 1 && r->val1.getValue() == 0;
}

std::optional<Node> bitConstraint(const Node& fact)
{
  SpectrumOpt r = spectrum(fact);
  if (r.has_value() && r->degree == 2 && r->val0.getValue() == 0
      && r->val1.getValue() == 0)
  {
    return {r->var};
  }
  return {};
}

namespace {

/**
 * Given spectra for f and g, compute an (optional) spectrum for f @ g, where @
 * is point-wise operation
 *
 * @param a spectrum for f
 * @param b spectrum for g
 * @param dOp binary operator on uint8_t for computing the degree of f @ g
 * @param fOp the binary point-wise operator @
 *
 * */
template <typename DegreeOp, typename FieldOp>
SpectrumOpt spectrumOp(SpectrumOpt&& a,
                       SpectrumOpt&& b,
                       DegreeOp dOp,
                       FieldOp fOp)
{
  if (!(a.has_value() && b.has_value()))
  {
    // failed child
    return {};
  }
  if (a->degree && b->degree && a->var != b->var)
  {
    // multivariate
    return {};
  }
  uint8_t degree = dOp(a->degree, b->degree);
  if (degree > 2)
  {
    // high-degree
    return {};
  }
  FiniteFieldValue val0 = fOp(a->val0, b->val0);
  FiniteFieldValue val1 = fOp(a->val1, b->val1);
  Node&& var = a->degree ? std::move(a->var) : std::move(b->var);
  return {{var, degree, val0, val1}};
};

SpectrumOpt spectrum(const Node& t, uint8_t depth)
{
  if (t.getKind() == Kind::NOT)
  {
    return {};
  }
  Assert(t.getType().isFiniteField() || t.getKind() == Kind::EQUAL) << t;
  if (isFfLeaf(t))
  {
    if (t.isConst())
    {
      // this is a constant
      FiniteFieldValue v = t.getConst<FiniteFieldValue>();
      return {{Node::null(), 0, v, v}};
    }

    // this is an (ff) variable
    const Integer modulus = t.getType().getFfSize();
    return {{t, 1, {1, modulus}, {0, modulus}}};
  }
  switch (t.getKind())
  {
    case Kind::FINITE_FIELD_ADD:
    {
      SpectrumOpt acc = spectrum(t[0], depth - 1);
      for (size_t i = 1, n = t.getNumChildren(); i < n; ++i)
      {
        acc = spectrumOp(
            std::move(acc),
            spectrum(t[i], depth - 1),
            [](const uint8_t& x, const uint8_t& y) { return std::max(x, y); },
            [](const FiniteFieldValue& x, const FiniteFieldValue& y) {
              return x + y;
            });
      }
      return acc;
    }
    case Kind::EQUAL:
    {
      return spectrumOp(
          spectrum(t[0], depth - 1),
          spectrum(t[1], depth - 1),
          [](const uint8_t& x, const uint8_t& y) { return std::max(x, y); },
          [](const FiniteFieldValue& x, const FiniteFieldValue& y) {
            return x - y;
          });
    }
    case Kind::FINITE_FIELD_MULT:
    {
      SpectrumOpt acc = spectrum(t[0], depth - 1);
      for (size_t i = 1, n = t.getNumChildren(); i < n; ++i)
      {
        acc = spectrumOp(
            std::move(acc),
            spectrum(t[i], depth - 1),
            [](const uint8_t& x, const uint8_t& y) { return x + y; },
            [](const FiniteFieldValue& x, const FiniteFieldValue& y) {
              return x * y;
            });
      }
      return acc;
    }
    case Kind::FINITE_FIELD_BITSUM:
    {
      // give up
      return {};
    }
    default: Unreachable() << t.getKind();
  }
  return {};
}

}  // namespace

std::optional<std::pair<Node, FiniteFieldValue>> linearMonomial(const Node& t)
{
  TypeNode ty = t.getType();
  if (!ty.isFiniteField())
  {
    return {};
  }
  const Integer& p = ty.getFfSize();

  // X
  if (t.isVar())
  {
    return {{t, FiniteFieldValue(1, p)}};
  }

  // (ff.neg X)
  if (t.getKind() == Kind::FINITE_FIELD_NEG && t[0].isVar())
  {
    return {{t[0], FiniteFieldValue(-1, p)}};
  }

  // (ff.mul ? ?)
  if (t.getKind() == Kind::FINITE_FIELD_MULT && t.getNumChildren() == 2)
  {
    // (ff.mul k X)
    if (t[0].isConst() && t[1].isVar())
    {
      return {{t[1], t[0].getConst<FiniteFieldValue>()}};
    }

    // (ff.mul X k)
    if (t[1].isConst() && t[0].isVar())
    {
      return {{t[0], t[1].getConst<FiniteFieldValue>()}};
    }
  }

  return {};
}

std::optional<std::pair<std::vector<std::pair<Node, FiniteFieldValue>>,
                        std::vector<Node>>>
extractLinearMonomials(const Node& t)
{
  TypeNode ty = t.getType();
  if (!ty.isFiniteField())
  {
    return {};
  }
  if (t.getKind() != Kind::FINITE_FIELD_ADD)
  {
    return {};
  }
  std::vector<std::pair<Node, FiniteFieldValue>> monomials{};
  std::vector<Node> otherSummands{};

  for (const Node& summand : t)
  {
    auto monomial = linearMonomial(summand);
    if (monomial.has_value())
    {
      monomials.push_back(std::move(monomial.value()));
    }
    else
    {
      otherSummands.push_back(summand);
    }
  }

  return {{std::move(monomials), std::move(otherSummands)}};
}

std::optional<
    std::pair<std::vector<std::pair<FiniteFieldValue, std::vector<Node>>>,
              std::vector<Node>>>
bitSums(const Node& t, std::unordered_set<Node> bits)
{
  // 1. get linear monomials
  auto res = extractLinearMonomials(t);
  if (!res.has_value())
  {
    return {};
  }
  auto& [monomials, rest] = res.value();
  if (monomials.empty())
  {
    return {};
  }

  Trace("ff::parse::debug") << "bitSums start " << t << std::endl;

  // we'll need to build some monomials
  auto nm = NodeManager::currentNM();
  auto mkMonomial = [&nm](TNode n, const FiniteFieldValue& coeff) {
    return nm->mkNode(Kind::FINITE_FIELD_MULT, nm->mkConst(coeff), n);
  };

  // 2. choose a subset of monomials w/ unique coefficients
  // (preferring monomials with vars in bits)

  // that subset, as a (coeff -> var) map
  // later, we'll iterate over monomials by coeff; this map will give the var
  std::unordered_map<FiniteFieldValue, Node, FiniteFieldValueHashFunction>
      bitMonomials{};
  // that subset, as a priority_queue over (-abs(signed_int(coeff)), coeff)
  // later, we'll iterate over monomials in the coeff order given here
  std::priority_queue<std::pair<Integer, FiniteFieldValue>> q{};

  for (const auto& [var, coeff] : monomials)
  {
    // iterate over monomials: (var, coeff) pairs
    Trace("ff::parse::debug")
        << "bitMonomial " << coeff << " " << var << std::endl;

    auto it = bitMonomials.find(coeff);
    if (it == bitMonomials.end())
    {
      // new coefficient
      Trace("ff::parse::debug") << " fresh bit" << var << std::endl;
      bitMonomials.insert(it, {coeff, var});
      q.emplace(-coeff.toSignedInteger().abs(), coeff);
    }
    else if (bits.count(var) && !bits.count(it->second))
    {
      // old coefficient, bit var, & the old var is not a bit; evict it.
      Trace("ff::parse::debug")
          << " " << var << " evicts " << it->second << std::endl;
      rest.push_back(mkMonomial(it->second, coeff));
      it->second = var;
    }
    else
    {
      // skip
      Trace("ff::parse::debug")
          << " skipped " << coeff << " " << var << std::endl;
      Trace("ff::parse::debug")
          << "  isBit: " << std::boolalpha << !!bits.count(var) << std::endl;
      rest.push_back(mkMonomial(var, coeff));
    }
  }

  // 3. extact bitsums

  std::vector<std::pair<FiniteFieldValue, std::vector<Node>>> bitSums{};
  FiniteFieldValue two(2, t.getType().getFfSize());
  // choose a starting constant k; we'll search for a run: k*x, 2k*y, 4k*z, ...
  // we choose k from the priority queue (i.e., k with least abs(k) goes first)
  while (!q.empty())
  {
    FiniteFieldValue k = q.top().second;
    q.pop();

    // a list of variables x, y, z, ... in the discovered run
    std::vector<Node> bsBits{};

    // search for a run: k*x, 2k*y, 4k*z, ...
    FiniteFieldValue coeff = k;
    while (bitMonomials.count(coeff))
    {
      auto var = bitMonomials.at(coeff);
      bsBits.push_back(var);
      bitMonomials.erase(coeff);
      coeff *= two;
    }

    if (bsBits.size() > 1)
    {
      // save as a bitsum if the length is greater than 1
      bitSums.emplace_back(k, std::move(bsBits));
    }
    else if (bsBits.size() == 1)
    {
      // if one bit, add its summand to rest
      rest.push_back(mkMonomial(bsBits[0], coeff / two));
    }
  }

  Assert(bitMonomials.empty());
  Assert(q.empty());

  return {{std::move(bitSums), std::move(rest)}};
}

std::optional<Node> disjunctiveBitConstraint(const Node& t)
{
  if (t.getKind() == Kind::OR && t.getNumChildren() == 2
      && t[0].getKind() == Kind::EQUAL && t[1].getKind() == Kind::EQUAL
      && t[0][1].getType().isFiniteField() && t[1][0].getType().isFiniteField())
  {
    using theory::ff::parse::oneConstraint;
    using theory::ff::parse::zeroConstraint;
    if ((oneConstraint(t[0]) && zeroConstraint(t[1]))
        || (oneConstraint(t[1]) && zeroConstraint(t[0])))
    {
      return {theory::ff::parse::spectrum(t[0])->var};
    }
  }
  return {};
}

}  // namespace parse
}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal
