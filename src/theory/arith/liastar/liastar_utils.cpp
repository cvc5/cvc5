/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility functions for liastar extension.
 */

#include "liastar_utils.h"

#include "theory/datatypes/tuple_utils.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

Node LiaStarUtils::getVectorPredicate(Node n)
{
  Assert(n.getKind() == Kind::STAR_CONTAINS);
  Node variables = n[0];
  Node predicate = n[1];
  Node vec = n[2];

  std::unordered_set<Node> boundVariables;
  for (const auto& v : variables)
  {
    boundVariables.insert(v);
  }
  std::vector<Node> vecElements = datatypes::TupleUtils::getTupleElements(vec);
  Node substitute = predicate.substitute(variables.begin(),
                                         variables.end(),
                                         vecElements.begin(),
                                         vecElements.end());
  Trace("liastar-ext-debug") << "n: " << n << std::endl;
  Trace("liastar-ext-debug") << "predicate: " << predicate << std::endl;
  Trace("liastar-ext-debug") << "substitute: " << substitute << std::endl;
  return substitute;
}
}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal