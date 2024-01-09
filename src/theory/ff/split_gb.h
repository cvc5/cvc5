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
 * Finding common zeros using split groebner bases.
 *
 * The following procedures are from the paper:
 * * split: Split
 * * splitFindZero: SplitFindZero
 * * splitZeroExtend: SplitZeroExtend
 * * splitGb: SplitGb
 * * applyRule: ApplyRule
 * * admit: admit
 * * BitProp::getBitEqualities: extraProp
 */

#ifdef CVC5_USE_COCOA

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FF__SPLIT_GB_H
#define CVC5__THEORY__FF__SPLIT_GB_H

// external includes
#include <CoCoA/ideal.H>
#include <CoCoA/ring.H>
#include <CoCoA/symbol.H>

// std includes
#include <memory>
#include <optional>
#include <unordered_set>
#include <variant>
#include <vector>

// internal includes
#include "theory/ff/cocoa_encoder.h"
#include "theory/ff/cocoa_util.h"
#include "theory/ff/multi_roots.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

/** defined below */
class Gb;
/** defined below */
class BitProp;

/** A split GB. */
using SplitGb = std::vector<Gb>;

/** Find a model for these facts */
std::optional<FfModel> split(const std::vector<Node>& facts,
                             const FfSize& size);

/** Compute a split Gb. */
std::vector<Gb> splitGb(const std::vector<std::vector<Poly>>& generatorSets,
                        BitProp& bitProp);

/** Whether to admit p into ideal i. */
bool admit(size_t i, const Poly& p);

/** Find a zero for this split Gb */
std::optional<Point> splitFindZero(SplitGb&& splitBasis,
                                   CoCoA::ring polyRing,
                                   BitProp& bitProp);

/** Extend curR into a zero for this split Gb. */
std::variant<Point, Poly, bool> splitZeroExtend(
    const std::vector<Poly>& origPolys,
    const SplitGb&& curBases,
    const PartialPoint&& curR,
    const BitProp& bitProp);

/** Apply a branching rule. */
std::unique_ptr<AssignmentEnumerator> applyRule(const Gb& gb,
                                                const CoCoA::ring& polyRing,
                                                const PartialPoint& r);

/** Check wether this point is a zero. */
void checkZero(const SplitGb& origBases, const Point& zero);

/** Wraps a CoCoA GBasis, but supports an empty basis. */
class Gb
{
 public:
  Gb();
  Gb(const std::vector<Poly>& generators);
  bool contains(const Poly& p) const;
  bool isWholeRing() const;
  Poly reduce(const Poly& p) const;
  bool zeroDimensional() const;
  Poly minimalPolynomial(const Poly& p) const;
  const std::vector<Poly>& basis() const;

 private:
  std::optional<CoCoA::ideal> d_ideal;
  std::vector<Poly> d_basis;
};

/** Propagator for bit equalities from bitsum equalities. */
class BitProp
{
 public:
  BitProp(const std::vector<Node>& facts, CocoaEncoder& encoder);
  BitProp();
  /** get all known bit equalities from thes split basis */
  std::vector<Poly> getBitEqualities(const SplitGb& sgb);

 private:
  /** terms that are known to be 0 or 1 */
  std::unordered_set<Node> d_bits;
  /** known bitsums */
  std::vector<Node> d_bitsums;
  /** the ambiant encoding of terms into Cocoa */
  CocoaEncoder* d_enc;
};

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__SPLIT_GB_H */

#endif /* CVC5_USE_COCOA */
