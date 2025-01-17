/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * a split groebner basis
 */

#ifdef CVC5_USE_COCOA

#include "theory/ff/split_gb.h"

// external includes
#include <CoCoA/BigIntOps.H>
#include <CoCoA/SparsePolyIter.H>
#include <CoCoA/SparsePolyOps-MinPoly.H>
#include <CoCoA/SparsePolyOps-RingElem.H>
#include <CoCoA/SparsePolyOps-ideal.H>
#include <CoCoA/SparsePolyRing.H>

// std includes
#include <variant>

// internal includes
#include "base/output.h"
#include "theory/ff/parse.h"
#include "util/resource_manager.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

std::optional<std::unordered_map<Node, FiniteFieldValue>> split(
    const std::vector<Node>& facts, const FfSize& size, const Env& env)
{
  std::unordered_set<Node> bits{};
  CocoaEncoder enc(env.getNodeManager(), size);
  for (const auto& fact : facts)
  {
    enc.addFact(fact);
  }
  enc.endScan();
  for (const auto& fact : facts)
  {
    enc.addFact(fact);
  }

  Polys nlGens = enc.polys();
  Polys lGens = enc.bitsumPolys();
  for (const auto& p : enc.polys())
  {
    if (CoCoA::deg(p) <= 1)
    {
      lGens.push_back(p);
    }
  }

  BitProp bitProp(facts, enc);

  std::vector<Polys> splitGens = {lGens, nlGens};
  SplitGb splitBasis = splitGb(splitGens, bitProp, env);
  if (std::any_of(splitBasis.begin(), splitBasis.end(), [](const auto& b) {
        return b.isWholeRing();
      }))
  {
    return {};
  }

  std::optional<Point> root =
      splitFindZero(std::move(splitBasis), enc.polyRing(), bitProp, env);
  if (root.has_value())
  {
    std::unordered_map<Node, FiniteFieldValue> model;
    for (const auto& [indetIdx, varNode] : enc.nodeIndets())
    {
      FiniteFieldValue literal = enc.cocoaFfToFfVal(root.value()[indetIdx]);
      Trace("ff::model") << "Model: " << varNode << " = " << literal
                         << std::endl;
      model.insert({varNode, literal});
    }
    return model;
  }
  return {};
}

SplitGb splitGb(const std::vector<Polys>& generatorSets,
                BitProp& bitProp,
                const Env& env)
{
  size_t k = generatorSets.size();
  std::vector<Polys> newPolys(generatorSets);
  SplitGb splitBasis(k);
  do
  {
    // add newPolys to each basis
    for (size_t i = 0; i < k; ++i)
    {
      if (newPolys[i].size())
      {
        Polys newGens{};

        const auto& basis = splitBasis[i].basis();
        std::copy(basis.begin(), basis.end(), std::back_inserter(newGens));
        std::copy(newPolys[i].begin(),
                  newPolys[i].end(),
                  std::back_inserter(newGens));
        splitBasis[i] = Gb(newGens, env.getResourceManager());
        newPolys[i].clear();
      }
    }

    // compute polys that can be shared
    Polys toPropagate = bitProp.getBitEqualities(splitBasis);
    for (size_t i = 0; i < k; ++i)
    {
      const auto& basis = splitBasis[i].basis();
      std::copy(basis.begin(), basis.end(), std::back_inserter(toPropagate));
    }

    // share polys with ideals that accept them.
    for (const auto& p : toPropagate)
    {
      for (size_t j = 0; j < k; ++j)
      {
        if (admit(j, p) && !splitBasis[j].contains(p))
        {
          newPolys[j].push_back(p);
        }
      }
    }
  } while (std::any_of(newPolys.begin(), newPolys.end(), [](const auto& s) {
    return s.size();
  }));
  return splitBasis;
}

bool admit(size_t i, const Poly& p)
{
  Assert(i < 2);
  return CoCoA::deg(p) <= 1 && (i == 0 || CoCoA::NumTerms(p) <= 2);
}

std::optional<Point> splitFindZero(SplitGb&& splitBasisIn,
                                   CoCoA::ring polyRing,
                                   BitProp& bitProp,
                                   const Env& env)
{
  SplitGb splitBasis = std::move(splitBasisIn);
  while (true)
  {
    Polys allGens{};
    for (const auto& b : splitBasis)
    {
      std::copy(
          b.basis().begin(), b.basis().end(), std::back_inserter(allGens));
    }
    PartialPoint nullPartialRoot(CoCoA::NumIndets(polyRing));
    auto result = splitZeroExtend(
        allGens, SplitGb(splitBasis), std::move(nullPartialRoot), bitProp, env);
    if (std::holds_alternative<Poly>(result))
    {
      auto conflict = std::get<Poly>(result);
      std::vector<Polys> gens{};
      for (auto& b : splitBasis)
      {
        gens.push_back({});
        std::copy(b.basis().begin(),
                  b.basis().end(),
                  std::back_inserter(gens.back()));
        gens.back().push_back(conflict);
      }
      splitBasis = splitGb(gens, bitProp, env);
    }
    else if (std::holds_alternative<bool>(result))
    {
      return {};
    }
    else
    {
      return {std::get<Point>(result)};
    }
  }
}

std::variant<Point, Poly, bool> splitZeroExtend(const Polys& origPolys,
                                                const SplitGb&& curBases,
                                                const PartialPoint&& curR,
                                                const BitProp& bitProp,
                                                const Env& env)
{
  Assert(origPolys.size());
  CoCoA::ring polyRing = CoCoA::owner(origPolys[0]);
  SplitGb bases(std::move(curBases));
  PartialPoint r(std::move(curR));
  long nAssigned = std::count_if(
      r.begin(), r.end(), [](const auto& v) { return v.has_value(); });
  if (std::any_of(bases.begin(), bases.end(), [](const Gb& i) {
        return i.isWholeRing();
      }))
  {
    for (const auto& p : origPolys)
    {
      auto value = cocoaEval(p, r);
      if (value.has_value() && !CoCoA::IsZero(*value) && !bases[0].contains(p))
      {
        return p;
      }
    }
    return false;
  }

  if (env.getResourceManager()->outOfTime())
  {
    throw FfTimeoutException("splitZeroExtend");
  }

  if (nAssigned == CoCoA::NumIndets(CoCoA::owner(origPolys[0])))
  {
    Point out;
    for (const auto& v : r)
    {
      out.push_back(*v);
    }
    return out;
  }
  auto brancher = applyRule(bases[0], polyRing, r);
  for (auto next = brancher->next(); next.has_value(); next = brancher->next())
  {
    long var = CoCoA::UnivariateIndetIndex(*next);
    Assert(var >= 0);
    Scalar val = -CoCoA::ConstantCoeff(*next);
    Assert(!r[var].has_value());
    PartialPoint newR = r;
    newR[var] = {val};
    Trace("ff::split::mc::debug")
        << std::string(1 + nAssigned, ' ') << CoCoA::indet(polyRing, var)
        << " = " << val << std::endl;
    std::vector<Polys> newSplitGens{};
    for (const auto& b : bases)
    {
      newSplitGens.push_back({});
      std::copy(b.basis().begin(),
                b.basis().end(),
                std::back_inserter(newSplitGens.back()));
      newSplitGens.back().push_back(*next);
    }
    BitProp bitPropCopy = bitProp;
    SplitGb newBases = splitGb(newSplitGens, bitPropCopy, env);
    auto result = splitZeroExtend(
        origPolys, std::move(newBases), std::move(newR), bitPropCopy, env);
    if (!std::holds_alternative<bool>(result))
    {
      return result;
    }
  }
  return false;
}

std::unique_ptr<AssignmentEnumerator> applyRule(const Gb& gb,
                                                const CoCoA::ring& polyRing,
                                                const PartialPoint& r)
{
  Assert(static_cast<long>(r.size()) == CoCoA::NumIndets(polyRing));
  Assert(std::any_of(
      r.begin(), r.end(), [](const auto& v) { return !v.has_value(); }));
  // (1) are there any polynomials that are univariate in an unassigned
  // variable?
  const auto& gens = gb.basis();
  for (const auto& p : gens)
  {
    int varNumber = CoCoA::UnivariateIndetIndex(p);
    if (varNumber >= 0 && !r[varNumber].has_value())
    {
      return factorEnumerator(p);
    }
  }
  // (2) if dimension 0, then compute such a polynomial
  if (gb.zeroDimensional())
  {
    // If zero-dimensional, we compute a minimal polynomial in some unset
    // variable.
    for (size_t i = 0, n = r.size(); i < n; ++i)
    {
      if (!r[i].has_value())
      {
        Poly minPoly = gb.minimalPolynomial(CoCoA::indet(polyRing, i));
        return factorEnumerator(minPoly);
      }
    }
    Unreachable() << "There should be some unset var";
  }
  else
  {
    // If positive dimension, we make a list of unset variables and
    // round-robin guess.
    //
    // TODO(aozdemir): better model construction (cvc5-wishues/issues/138)
    Polys toGuess{};
    for (size_t i = 0, n = r.size(); i < n; ++i)
    {
      if (!r[i].has_value())
      {
        toGuess.push_back(CoCoA::indet(polyRing, i));
      }
    }
    return std::make_unique<RoundRobinEnumerator>(toGuess,
                                                  polyRing->myBaseRing());
  }
  Unreachable();
  return nullptr;
}

void checkZero(const SplitGb& origBases, const Point& zero)
{
  for (const auto& b : origBases)
  {
    for (const auto& gen : b.basis())
    {
      auto value = cocoaEval(gen, zero);
      if (!CoCoA::IsZero(value))
      {
        std::stringstream o;
        o << "Bad zero!" << std::endl
          << "Generator " << gen << std::endl
          << "evaluated to " << value << std::endl
          << "under point: " << std::endl;
        for (size_t i = 0, n = zero.size(); i < n; ++i)
        {
          o << " " << CoCoA::indet(CoCoA::owner(gen), i) << " -> " << zero[i]
            << std::endl;
        }
        Assert(CoCoA::IsZero(value)) << o.str();
      }
    }
  }
}

Gb::Gb() : d_ideal(), d_basis(){};
Gb::Gb(const std::vector<Poly>& generators, const ResourceManager* rm)
    : d_ideal(), d_basis()
{
  if (generators.size())
  {
    d_ideal.emplace(CoCoA::ideal(generators));
    d_basis = GBasisTimeout(d_ideal.value(), rm);
  }
}

bool Gb::contains(const Poly& p) const
{
  return d_ideal.has_value() && CoCoA::IsElem(p, d_ideal.value());
}
bool Gb::isWholeRing() const
{
  return d_ideal.has_value() && CoCoA::IsOne(d_ideal.value());
}
Poly Gb::reduce(const Poly& p) const
{
  return d_ideal.has_value() ? CoCoA::NF(p, d_ideal.value()) : p;
}
bool Gb::zeroDimensional() const
{
  return d_ideal.has_value() && CoCoA::IsZeroDim(d_ideal.value());
}
Poly Gb::minimalPolynomial(const Poly& var) const
{
  Assert(zeroDimensional());
  Assert(CoCoA::UnivariateIndetIndex(var) != -1);
  Poly minPoly = CoCoA::MinPolyQuot(var, *d_ideal, var);
  return minPoly;
}
const Polys& Gb::basis() const { return d_basis; }

BitProp::BitProp(const std::vector<Node>& facts, CocoaEncoder& encoder)
    : d_bits(), d_bitsums(encoder.bitsums()), d_enc(&encoder)
{
  for (const auto& fact : facts)
  {
    auto bs = parse::bitConstraint(fact);
    if (bs)
    {
      d_bits.insert(*bs);
    }
  }
}

BitProp::BitProp() : d_bits(), d_bitsums(), d_enc(nullptr) {}

Polys BitProp::getBitEqualities(const SplitGb& splitBasis)
{
  Polys output{};

  std::vector<Node> bitConstrainedBitsums{};

  std::vector<Node> nonConstantBitsums{};
  for (const auto& bitsum : d_bitsums)
  {
    // does any basis know `bitsum = k`?
    bool isConst = false;
    for (const auto& b : splitBasis)
    {
      Poly normal = b.reduce(d_enc->getTermEncoding(bitsum));
      if (CoCoA::IsConstant(normal))
      {
        // this basis b knows that bitsum is a constant
        Integer val =
            d_enc->cocoaFfToFfVal(CoCoA::ConstantCoeff(normal)).getValue();
        if (val >= Integer(2).pow(bitsum.getNumChildren()))
        {
          output.clear();
          output.push_back(CoCoA::one(d_enc->polyRing()));
          return output;
        }

        // check that all inputs are bit-constrained
        if (std::all_of(bitsum.begin(), bitsum.end(), [&](const Node& bit) {
              return isBit(bit, splitBasis);
            }))
        {
          // propagate `bits(bitsum) = bits(k)`
          for (size_t i = 0, n = bitsum.getNumChildren(); i < n; ++i)
          {
            auto bit = val.isBitSet(i) ? CoCoA::one(d_enc->polyRing())
                                       : CoCoA::zero(d_enc->polyRing());
            output.push_back(d_enc->getTermEncoding(bitsum[i]) - bit);
          }
          isConst = true;
          break;
        }
      }
    }
    // no basis knows this bitsum is a constant :(
    if (!isConst)
    {
      nonConstantBitsums.push_back(bitsum);
    }
  }

  // for all pairs of non-constant bitsums (a, b)
  for (size_t i = 0, n = nonConstantBitsums.size(); i < n; ++i)
  {
    for (size_t j = 0; j < i; ++j)
    {
      Node a = nonConstantBitsums[i];
      Node b = nonConstantBitsums[j];
      Poly bsDiff = d_enc->getTermEncoding(a) - d_enc->getTermEncoding(b);
      if (std::any_of(
              splitBasis.begin(), splitBasis.end(), [&bsDiff](const auto& ii) {
                return ii.contains(bsDiff);
              }))
      {
        // this basis knows a = b
        Trace("ffl::bitprop")
            << " (= " << a << "\n    " << b << ")" << std::endl;
        size_t min = std::min(a.getNumChildren(), b.getNumChildren());
        size_t max = std::max(a.getNumChildren(), b.getNumChildren());
        if (max > d_enc->size().d_val.length())
        {
          Trace("ffl::bitprop") << " bitsum overflow" << std::endl;
          continue;
        }

        // check that all inputs to both a and b are bit-constrained
        bool allBits = true;
        for (const auto& sum : {a, b})
        {
          for (const auto& c : sum)
          {
            if (!isBit(c, splitBasis))
            {
              Trace("ffl::bitprop") << " non-bit " << c << std::endl;
              allBits = false;
            }
          }
        }

        if (!allBits) continue;

        // propagate `bits(a) = bits(b)`
        for (size_t k = 0; k < min; ++k)
        {
          Poly diff =
              d_enc->getTermEncoding(a[k]) - d_enc->getTermEncoding(b[k]);
          output.push_back(diff);
        }

        if (a.getNumChildren() != min || b.getNumChildren() != min)
        {
          // bitsums have different lengths: propagate zeros for the longer part
          Node longer = b.getNumChildren() > min ? b : a;
          for (size_t k = min; k < max; ++k)
          {
            Poly isZero = d_enc->getTermEncoding(longer[k]);
            output.push_back(isZero);
          }
        }
      }
    }
  }
  return output;
}

bool BitProp::isBit(const Node& possibleBit, const SplitGb& splitBasis)
{
  if (d_bits.count(possibleBit))
  {
    return true;
  }
  Poly p = d_enc->getTermEncoding(possibleBit);
  Poly bitConstraint = p * p - p;
  if (std::any_of(splitBasis.begin(),
                  splitBasis.end(),
                  [&bitConstraint](const auto& ii) {
                    return ii.contains(bitConstraint);
                  }))
  {
    Trace("ffl::bitprop") << " bit through GB " << possibleBit << std::endl;
    d_bits.insert(possibleBit);
    return true;
  }
  return false;
}

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_COCOA */
