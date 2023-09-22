/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implements a way to track the origins of ICP-style contractions.
 */

#ifndef CVC5__THEORY__ARITH__ICP__CONTRACTION_ORIGINS_H
#define CVC5__THEORY__ARITH__ICP__CONTRACTION_ORIGINS_H

#include <memory>
#include <vector>

#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {
namespace icp {

/**
 * This class tracks origins of ICP-style contractions of variable intervals.
 * For every variable, it holds one origin object that may recursively depend on
 * previous contraction origins. Initially, a immediate bound on a variable
 * (like x>0) yields an origin for this variable. For every contraction, we then
 * add a new origin that recursively holds the old origins, usually those of all
 * variables involved in the contraction. When generating a conflict or a lemma,
 * a recursive walk through this structure allow to retrieve all input theory
 * atoms that contributed to the new fact or the conflict.
 */
class ContractionOriginManager
{
 public:
  /**
   * Origin of one particular contraction step.
   * Usually, this is either a direct bound or the application of a contraction
   * candidate. The direct bound is stored in the candidate while origins
   * remains empty. The contraction candidate is stored in the candidate while
   * origins hold the origins of all variables used in the contraction.
   */
  struct ContractionOrigin
  {
    /** The theory atom used to do this contraction. */
    Node candidate;
    /** All origins required for this contraction. */
    std::vector<ContractionOrigin*> origins;
  };

 private:
  /**
   * Recursively walks through the data structure, collecting all theory atoms.
   */
  void getOrigins(ContractionOrigin const* const origin,
                  std::set<Node>& res) const;

 public:
  /** Return the current origins for all variables. */
  const std::map<Node, ContractionOrigin*>& currentOrigins() const;
  /**
   * Add a new contraction for the targetVariable.
   * Adds a new origin with the given candidate and origins.
   * If addTarget is set to true, we also add the current origin of the
   * targetVariable to origins. This corresponds to whether we intersected the
   * new interval with the previous interval, or whether the new interval was a
   * subset of the previous one in the first place.
   */
  void add(const Node& targetVariable,
           const Node& candidate,
           const std::vector<Node>& originVariables,
           bool addTarget = true);

  /**
   * Collect all theory atoms from the origins of the given variable.
   */
  std::vector<Node> getOrigins(const Node& variable) const;

  /** Check whether a node c is among the origins of a variable. */
  bool isInOrigins(const Node& variable, const Node& c) const;

 private:
  /** The current origins for every variable. */
  std::map<Node, ContractionOrigin*> d_currentOrigins;
  /** All allocated origins to allow for proper deallocation. */
  std::vector<std::unique_ptr<ContractionOrigin>> d_allocations;
};

/** Stream the constration origins to an ostream. */
std::ostream& operator<<(std::ostream& os, const ContractionOriginManager& com);

}  // namespace icp
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif
