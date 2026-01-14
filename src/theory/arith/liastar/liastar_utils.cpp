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
#include "theory/rewriter.h"
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

Node LiaStarUtils::toDNF(Node n, Env* e)
{
  Assert(n.getType().isBoolean());
  Node dnf = n;
  bool changed = false;
  do
  {
    std::tie(dnf, changed) = LiaStarUtils::booleanDNF(dnf, e);
  } while (changed);
  return dnf;
}

std::pair<Node, bool> LiaStarUtils::booleanDNF(Node n, Env* e)
{
  NodeManager* nm = e->getNodeManager();
  auto rw = e->getRewriter();
  switch (n.getKind())
  {
    case Kind::GEQ: return {n, false};
    case Kind::EQUAL:
    {
      Node l = nm->mkNode(Kind::GEQ, n[0], n[1]);
      Node r = nm->mkNode(Kind::GEQ, n[1], n[0]);
      return {nm->mkNode(Kind::OR, l, r), true};
    }
    case Kind::ITE:
    {
      Node l = n[0].andNode(n[1]);
      Node r = rw->rewrite(n[0].notNode().andNode(n[2]));
      return {nm->mkNode(Kind::OR, l, r), true};
    }
    case Kind::AND:
    {
      bool leftBool = false;
      Node leftNode = n[0];
      do
      {
        std::tie(leftNode, leftBool) = LiaStarUtils::booleanDNF(leftNode, e);
      } while (leftBool);
      bool rightBool = false;
      Node rightNode = n[1];
      do
      {
        std::tie(rightNode, rightBool) = LiaStarUtils::booleanDNF(rightNode, e);
      } while (rightBool);
      // check if any of the children is a disjunction
      if (leftNode.getKind() == Kind::OR)
      {
        // (A or B) and C <=> (A and B) or (B and C)
        Node l = leftNode[0].andNode(rightNode);
        Node r = leftNode[1].andNode(rightNode);
        return {l.orNode(r), true};
      }
      if (rightNode.getKind() == Kind::OR)
      {
        // A and (B or C)  <=> (A and B) or (A and C)
        Node l = leftNode.andNode(rightNode[0]);
        Node r = leftNode.andNode(rightNode[1]);
        return {l.orNode(r), true};
      }
      Node computed = nm->mkNode(Kind::AND, leftNode, rightNode);
      if (computed == n)
      {
        return {n, false};
      }
      return {computed, true};
    }
    case Kind::OR:
    {
      bool leftBool = false;
      Node leftNode = n[0];
      do
      {
        std::tie(leftNode, leftBool) = LiaStarUtils::booleanDNF(leftNode, e);
      } while (leftBool);
      bool rightBool = false;
      Node rightNode = n[1];
      do
      {
        std::tie(rightNode, rightBool) = LiaStarUtils::booleanDNF(rightNode, e);
      } while (rightBool);

      Node computed = nm->mkNode(Kind::OR, leftNode, rightNode);
      if (computed == n)
      {
        return {n, false};
      }
      return {computed, true};
    }
    default:
    {
      std::cout << "n: " << n << ", kind: " << n.getKind() << std::endl;
      throw "Unexpected kind";
    }
  }
}

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal