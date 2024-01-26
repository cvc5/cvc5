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
 * encoding Nodes as cocoa ring elements.
 */

#include "cvc5_private.h"

#ifdef CVC5_USE_COCOA

#ifndef CVC5__THEORY__FF__COCOA_H
#define CVC5__THEORY__FF__COCOA_H

// external includes
#include <CoCoA/ring.H>
#include <CoCoA/symbol.H>

// std includes
#include <optional>
#include <string>
#include <unordered_map>
#include <unordered_set>

// internal includes
#include "expr/node.h"
#include "theory/ff/cocoa_util.h"
#include "theory/ff/util.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

/**
 *  Create cocoa symbol, sanitizing varName.
 *  If index is given, subscript the symbol by it.
 */
CoCoA::symbol cocoaSym(const std::string& varName,
                       std::optional<size_t> index = {});

/**
 * Class for encoding a Node as a Poly.
 *
 * Requires two passes over the nodes. On the first pass it collects variables,
 * !=s, and bitsums. On the second, it encodes. The first stage is called
 * "Stage::Scan", the second is "Stage::Encode".
 *
 * Two stages are necessary because when creating a CoCoA polynomial ring, one
 * must declare all the variables up-front. So, before we create any polynomials
 * (to encode terms), we must know all the (CoCoA) variables. CoCoA variables
 * are used to encode cvc5 variables, bitsums, and witnesses of disequality (a
 * != b is encoded as (a - b)w = 1, where w is the witness).
 */
class CocoaEncoder : public FieldObj
{
 public:
  /** Create a new encoder, for this field. */
  CocoaEncoder(const FfSize& size);
  /** Add a fact (one must call this twice per fact, once per stage). */
  void addFact(const Node& fact);
  /** Start Stage::Encode. */
  void endScan();
  /**
   * Get the polys who's common zero we are finding (excluding bitsums).
   * Available in Stage::Encode.
   */
  const std::vector<Poly>& polys() const { return d_polys; }
  /**
   * Get the bitsum polys.
   * These have form: x - b0 - 2*b1 - 4b2 ... - 2^n*b_n.
   * Available in Stage::Encode.
   */
  const std::vector<Poly>& bitsumPolys() const { return d_bitsumPolys; }
  /**
   * Get the poly for this term
   * Available in Stage::Encode.
   */
  const Poly& getTermEncoding(const Node& t) const { return d_cache.at(t); }
  /**
   * Get the bitsum terms (for the bitsumPolys).
   * Available in Stage::Encode.
   */
  std::vector<Node> bitsums() const;
  /**
   * The poly ring we've encoded into.
   * Available in Stage::Encode.
   */
  const CoCoA::ring& polyRing() const { return d_polyRing.value(); }
  /**
   * A list of (indeterminant num, Node) pairs. Useful for extracting a model.
   * Available in Stage::Encode.
   */
  std::vector<std::pair<size_t, Node>> nodeIndets() const;
  /**
   * Convert a (coefficient) Scalar to a FiniteFieldValue.
   */
  FiniteFieldValue cocoaFfToFfVal(const Scalar& elem);

 private:
  /**
   * Get a fresh symbol that starts with varName.
   * If index is given, subscript the symbol by it.
   */
  CoCoA::symbol freshSym(const std::string& varName,
                         std::optional<size_t> index = {});
  /** a bitsum or a var */
  const Node& symNode(CoCoA::symbol s) const;
  /** have we assigned this symbol to some Node? */
  bool hasNode(CoCoA::symbol s) const;
  /** get the poly for this symbol */
  const Poly& symPoly(CoCoA::symbol s) const;
  /** encode this term as a poly (caching) */
  void encodeTerm(const Node& t);
  /** encode this fact as a poly that must be zero (caching) */
  void encodeFact(const Node& f);

  /** Which pass we're in. */
  enum class Stage
  {
    /** collecting: variable, !=, bitsum */
    Scan,
    /** encoding terms */
    Encode,
  };

  // configuration

  /** the stage that we're in; initially scanning */
  Stage d_stage{Stage::Scan};

  // populated during Stage::Scan

  /** all nodes scanned */
  std::unordered_set<Node> d_scanned{};
  /** all variables seen */
  std::unordered_set<std::string> d_vars{};
  /** map: bitsum term to its symbol */
  std::unordered_map<Node, CoCoA::symbol> d_bitsumSyms{};
  /** map: variable term to its symbol */
  std::unordered_map<Node, CoCoA::symbol> d_varSyms{};
  /** map: term (a != b) to the symbol for the inverse of (a - b) */
  std::unordered_map<Node, CoCoA::symbol> d_diseqSyms{};
  /** all symbols */
  std::vector<CoCoA::symbol> d_syms{};
  /** map: symbol name to polynomial */
  std::unordered_map<std::string, Poly> d_symPolys{};
  /** map: symbol name to term */
  std::unordered_map<std::string, Node> d_symNodes{};

  // populated at the end of Stage::Scan

  /** the polynomial ring */
  std::optional<CoCoA::ring> d_polyRing{};

  // populated during Stage::Encode

  /** encoding cache */
  std::unordered_map<Node, Poly> d_cache{};
  /** polynomials that must be zero (except bitsums) */
  std::vector<Poly> d_polys{};
  /** bitsum polynomials that must be zero */
  std::vector<Poly> d_bitsumPolys{};
};

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__COCOA_H */

#endif /* CVC5_USE_COCOA */
