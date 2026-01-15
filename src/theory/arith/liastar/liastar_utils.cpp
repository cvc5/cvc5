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
  Assert(n.getType().isBoolean());
  NodeManager* nm = e->getNodeManager();
  Node falseConst = nm->mkConst<bool>(false);
  Node trueConst = nm->mkConst<bool>(true);
  auto rw = e->getRewriter();
  Kind k = n.getKind();
  switch (k)
  {
    case Kind::CONST_BOOLEAN: return {n, false};

    case Kind::GEQ:
    {
      // (>=
      //    (ite (>= x y) a b)
      //    (ite (>= x z) c d))
      // should return
      // (or
      //   (and (>= x y) (>= x z)              (>= a c))
      //   (and (>= x y) (>= z (+ x 1))        (>= a d))
      //   (and (>= y (+ x 1)) (>= x z))       (>= b c))
      //   (and (>= y (+ x 1)) (>= z (+ x 1))) (>= b d))
      std::vector<std::pair<Node, Node>> left = integerDNF(n[0], e);
      std::vector<std::pair<Node, Node>> right = integerDNF(n[1], e);
      if (left.size() == 1 && right.size() == 1)
      {
        return {n, false};
      }
      Node geq = falseConst;
      // combine the conditions of left and right
      for (const auto& l : left)
      {
        for (const auto& r : right)
        {
          Node result = nm->mkNode(k, l.second, r.second);
          Node combined;
          if (l.first == trueConst && r.first == trueConst)
          {
            combined = result;
          }
          else if (l.first == trueConst && r.first != trueConst)
          {
            combined = result.andNode(r.first);
          }
          else if (l.first != trueConst && r.first == trueConst)
          {
            combined = result.andNode(l.first);
          }
          else
          {
            combined = result.andNode(l.first).andNode(r.first);
          }
          if (geq == falseConst)
          {
            geq = combined;
          }
          else
          {
            geq = geq.orNode(combined);
          }
        }
      }
      return {geq, true};
    }
    case Kind::EQUAL:
    {
      if (n[0].getType().isInteger())
      {
        // (=
        //    (ite (>= x y) a b)
        //    (ite (>= x z) c d))
        // should return
        // (or
        //   (and (>= x y) (>= x z)              (>= a c) (>= c a))
        //   (and (>= x y) (>= z (+ x 1))        (>= a d) (>= d a))
        //   (and (>= y (+ x 1)) (>= x z))       (>= b c) (>= c b))
        //   (and (>= y (+ x 1)) (>= z (+ x 1))) (>= b d) (>= d b))
        std::vector<std::pair<Node, Node>> left = integerDNF(n[0], e);
        std::vector<std::pair<Node, Node>> right = integerDNF(n[1], e);
        if (left.size() == 1 && right.size() == 1)
        {
          Node l = nm->mkNode(Kind::GEQ, n[0], n[1]);
          Node r = nm->mkNode(Kind::GEQ, n[1], n[0]);
          return {l.andNode(r), false};
        }
        Node eq = falseConst;
        // combine the conditions of left and right
        for (const auto& l : left)
        {
          for (const auto& r : right)
          {
            Node geq1 = nm->mkNode(Kind::GEQ, l.second, r.second);
            Node geq2 = nm->mkNode(Kind::GEQ, r.second, l.second);
            Node result = geq1.andNode(geq2);
            Node combined;
            if (l.first == trueConst && r.first == trueConst)
            {
              combined = result;
            }
            else if (l.first == trueConst && r.first != trueConst)
            {
              combined = result.andNode(r.first);
            }
            else if (l.first != trueConst && r.first == trueConst)
            {
              combined = result.andNode(l.first);
            }
            else
            {
              combined = result.andNode(l.first).andNode(r.first);
            }
            if (eq == falseConst)
            {
              eq = combined;
            }
            else
            {
              eq = eq.orNode(combined);
            }
          }
        }
        return {eq, true};
      }
      break;
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
    case Kind::NOT:
    {
      Kind kind = n[0].getKind();
      switch (kind)
      {
        case Kind::NOT:
        {
          // (not (not a)) is rewritten as just a
          Node ret = rw->rewrite(n[0][0]);
          return {ret, true};
        }
        case Kind::GEQ:
        {
          //(not (>= a b)) is rewritten as (>= b (+ a 1))
          Node a = n[0][0];
          Node b = n[0][1];
          Node aPlusOne = nm->mkNode(Kind::ADD, a, nm->mkConstInt(Rational(1)));
          Node ret = nm->mkNode(kind, b, aPlusOne);
          return {ret, true};
        }
        case Kind::OR:
        {
          // (not (or a b)) is rewritten as (and (not a) (not b))
          Node a = n[0][0].notNode();
          Node b = n[0][1].notNode();
          Node ret = nm->mkNode(Kind::AND, a, b);
          ret = rw->rewrite(ret);
          return {ret, true};
        }
        case Kind::AND:
        {
          // (not (and a b)) is rewritten as (or (not a) (not b))
          Node a = n[0][0].notNode();
          Node b = n[0][1].notNode();
          Node ret = nm->mkNode(Kind::OR, a, b);
          ret = rw->rewrite(ret);
          return {ret, true};
        }
        default: break;
      }
      break;
    }
    default:
    {
      std::cout << "n: " << n << ", kind: " << n.getKind() << std::endl;
      throw "Unexpected kind";
    }
  }
}

std::vector<std::pair<Node, Node>> LiaStarUtils::integerDNF(Node n, Env* e)
{
  Assert(n.getType().isInteger());
  NodeManager* nm = e->getNodeManager();
  Node trueConst = nm->mkConst<bool>(true);
  auto rw = e->getRewriter();
  Kind k = n.getKind();
  switch (k)
  {
    case Kind::BOUND_VARIABLE:
    case Kind::CONST_INTEGER: return {{trueConst, n}};
    case Kind::ADD:
    case Kind::SUB:
    case Kind::MULT:
    {
      // (+
      //    (ite (>= x y) a b)
      //    (ite (>= x z) c d))
      // should return 4 cases
      // <(and (>= x y) (>= x z))            ,(+ a c)>
      // <(and (>= x y) (>= z (+ x 1)))      ,(+ a d)>
      // <(and (>= y (+ x 1)) (>= x z))      ,(+ b c)>
      // <(and (>= y (+ x 1)) (>= z (+ x 1))),(+ b d)>
      std::vector<std::pair<Node, Node>> left = integerDNF(n[0], e);
      std::vector<std::pair<Node, Node>> right = integerDNF(n[1], e);
      std::vector<std::pair<Node, Node>> combined;
      // combine the conditions of left and right
      for (const auto& l : left)
      {
        for (const auto& r : right)
        {
          Node condition = rw->rewrite(l.first.andNode(r.first));
          Node result = rw->rewrite(nm->mkNode(k, l.second, r.second));
          combined.push_back({condition, result});
        }
      }
      return combined;
    }
    case Kind::ITE:
    {
      std::vector<std::pair<Node, Node>> iteResult;
      Node condition = toDNF(n[0], e);
      std::vector<std::pair<Node, Node>> thenDNF = integerDNF(n[1], e);
      for (const auto& pair : thenDNF)
      {
        Node newCondition;
        if (pair.first == trueConst)
        {
          newCondition = condition;
        }
        else
        {
          newCondition = pair.first.andNode(condition);
        }
        iteResult.push_back({newCondition, pair.second});
      }

      Node notCondition = rw->rewrite(condition.notNode());
      std::vector<std::pair<Node, Node>> elseDNF = integerDNF(n[2], e);
      for (const auto& pair : elseDNF)
      {
        Node newCondition;
        if (pair.first == trueConst)
        {
          newCondition = notCondition;
        }
        else
        {
          newCondition = pair.first.andNode(notCondition);
        }
        iteResult.push_back({newCondition, pair.second});
      }
      return iteResult;
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