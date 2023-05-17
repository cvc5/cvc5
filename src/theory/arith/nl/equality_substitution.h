/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * CAD-based solver based on https://arxiv.org/pdf/2003.05633.pdf.
 */

#ifndef CVC5__THEORY__ARITH__NL__EQUALITY_SUBSTITUTION_H
#define CVC5__THEORY__ARITH__NL__EQUALITY_SUBSTITUTION_H

#include <vector>

#include "context/context.h"
#include "expr/node.h"
#include "expr/node_algorithm.h"
#include "smt/env_obj.h"
#include "theory/substitutions.h"
#include "theory/theory.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

/**
 * This class is a general utility to eliminate variables from a set of
 * assertions.
 */
class EqualitySubstitution : protected EnvObj
{
 public:
  EqualitySubstitution(Env& env);
  /** Reset this object */
  void reset();

  /**
   * Eliminate variables using equalities from the set of assertions.
   * Returns a set of assertions where some variables may have been eliminated.
   * Substitutions for the eliminated variables can be obtained from
   * getSubstitutions().
   */
  std::vector<Node> eliminateEqualities(const std::vector<Node>& assertions);
  /**
   * Can be called after eliminateEqualities(). Returns the substitutions that
   * were found and eliminated.
   */
  const SubstitutionMap& getSubstitutions() const { return *d_substitutions; }
  /**
   * Can be called after eliminateEqualities(). Checks whether a direct conflict
   * was found, that is an assertion simplified to false during
   * eliminateEqualities().
   */
  bool hasConflict() const { return !d_conflict.empty(); }
  /**
   * Return the conflict found in eliminateEqualities() as a set of assertions
   * that is a subset of the input assertions provided to eliminateEqualities().
   */
  const std::vector<Node>& getConflict() const { return d_conflict; }
  /**
   * Postprocess a conflict found in the result of eliminateEqualities.
   * Replaces assertions within the conflict by their origins, i.e. the input
   * assertions and the assertions that gave rise to the substitutions being
   * used.
   */
  void postprocessConflict(std::vector<Node>& conflict) const;

 private:
  /** Utility method for addToConflictMap. Checks for n in d_conflictMap */
  void insertOrigins(std::set<Node>& dest, const Node& n) const;
  /** Add n -> { orig, *tracker } to the conflict map. The tracked nodes are
   * first resolved using d_trackOrigin, and everything is run through
   * insertOrigins to make sure that all origins are input assertions. */
  void addToConflictMap(const Node& n,
                        const Node& orig,
                        const std::set<TNode>& tracker);

  // The SubstitutionMap
  std::unique_ptr<SubstitutionMap> d_substitutions;
  // conflicting assertions, if a conflict was found
  std::vector<Node> d_conflict;
  // Maps a simplified assertion to the original assertion + set of original
  // assertions used for substitutions
  std::map<Node, std::vector<Node>> d_conflictMap;
  // Maps substituted terms (what will end up in the tracker) to the equality
  // from which the substitution was derived.
  std::map<Node, Node> d_trackOrigin;
};

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__NL__EQUALITY_SUBSTITUTION_H */
