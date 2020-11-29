/*********************                                                        */
/*! \file term_enumeration.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utilities for term enumeration
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__TERM_ENUMERATION_H
#define CVC4__THEORY__QUANTIFIERS__TERM_ENUMERATION_H

#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "expr/type_node.h"
#include "theory/type_enumerator.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

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
  TermEnumeration() {}
  ~TermEnumeration() {}
  /** get i^th term for type tn */
  Node getEnumerateTerm(TypeNode tn, unsigned i);
  /** may complete type
   *
   * Returns true if the type tn is closed enumerable, is interpreted as a
   * finite type, and has cardinality less than some reasonable value
   * (currently < 1000). This method caches the results of whether each type
   * may be completed.
   */
  bool mayComplete(TypeNode tn);
  /**
   * Static version of the above method where maximum cardinality is
   * configurable.
   */
  static bool mayComplete(TypeNode tn, unsigned cardMax);

  /** get domain
   *
   * If tn is a type such that mayComplete(tn) returns true, this method
   * adds all domain elements of tn to dom and returns true. Otherwise, this
   * method returns false.
   */
  bool getDomain(TypeNode tn, std::vector<Node>& dom);

 private:
  /** ground terms enumerated for types */
  std::unordered_map<TypeNode, std::vector<Node>, TypeNodeHashFunction>
      d_enum_terms;
  /** map from type to the index of its type enumerator in d_typ_enum. */
  std::unordered_map<TypeNode, size_t, TypeNodeHashFunction> d_typ_enum_map;
  /** type enumerators */
  std::vector<TypeEnumerator> d_typ_enum;
  /** closed enumerable type cache */
  std::unordered_map<TypeNode, bool, TypeNodeHashFunction> d_typ_closed_enum;
  /** may complete */
  std::unordered_map<TypeNode, bool, TypeNodeHashFunction> d_may_complete;
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__TERM_ENUMERATION_H */
