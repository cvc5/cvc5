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
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

std::pair<Node, Node> LiaStarUtils::getVectorPredicate(Node n, NodeManager* nm)
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
  Node nonnegativeConstraints = nm->mkConst<bool>(true);
  for (const auto& v : vecElements)
  {
    Node nonnegative = nm->mkNode(Kind::GEQ, v, nm->mkConstInt(Rational(0)));
    nonnegativeConstraints = nonnegativeConstraints.andNode(nonnegative);
  }
  Trace("liastar-ext-debug") << "substitute: " << substitute << std::endl;
  return std::make_pair(substitute, nonnegativeConstraints);
}
}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal