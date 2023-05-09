/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for term enumeration.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__TERM_ENUMERATION_H
#define CVC5__THEORY__QUANTIFIERS__TERM_ENUMERATION_H

#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "expr/type_node.h"
#include "theory/type_enumerator.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class QuantifiersBoundInference;

/** Term enumeration
 *
 * This class has utilities for enumerating terms. It stores
 * a cache of terms enumerated per each type.
 * It also has various utility functions regarding type
 * enumeration.
 */
class TermEnumeration
{
 public:
  TermEnumeration(QuantifiersBoundInference* qbi = nullptr);
  ~TermEnumeration() {}
  /** get i^th term for type tn */
  Node getEnumerateTerm(TypeNode tn, unsigned i);

  /** get domain
   *
   * If tn is a type such that d_qbi.mayComplete(tn) returns true, this method
   * adds all domain elements of tn to dom and returns true. Otherwise, this
   * method returns false.
   */
  bool getDomain(TypeNode tn, std::vector<Node>& dom);

 private:
  /**
   * Reference to quantifiers bound inference, which determines when it is
   * possible to enumerate the entire domain of a type. If this is not provided,
   * getDomain above always returns false.
   */
  QuantifiersBoundInference* d_qbi;
  /** ground terms enumerated for types */
  std::unordered_map<TypeNode, std::vector<Node>> d_enum_terms;
  /** map from type to the index of its type enumerator in d_typ_enum. */
  std::unordered_map<TypeNode, size_t> d_typ_enum_map;
  /** type enumerators */
  std::vector<TypeEnumerator> d_typ_enum;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__TERM_ENUMERATION_H */
