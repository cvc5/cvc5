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

#ifdef CVC5_USE_NORMALIZ

#include "liastar_utils.h"

#include "expr/algorithm/flatten.h"
#include "theory/booleans/theory_bool_rewriter.h"
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
  Node lambda = n[0];
  std::vector<Node> vars(lambda[0].begin(), lambda[0].end());
  std::vector<Node> vecElements(n.begin() + 1, n.end());

  Node substitute = lambda[1].substitute(
      vars.begin(), vars.end(), vecElements.begin(), vecElements.end());

  Trace("liastar-ext-debug") << "n: " << n << std::endl;
  Trace("liastar-ext-debug") << "predicate : " << lambda[1] << std::endl;
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
  // eliminate ites
  Node noItes = removeItes(n, e);
  Trace("liastar-ext-debug") << "noItes: " << noItes << std::endl;
  // eliminate negation
  Node nnf = removeNot(noItes, e);
  Trace("liastar-ext-debug") << "nnf: " << nnf << std::endl;
  if (TraceIsOn("liastar-ext-smt"))
  {
    // noItes
    Trace("liastar-ext-smt") << "(push 1)" << std::endl;
    Trace("liastar-ext-smt") << "(echo \"noItes\")" << std::endl;
    Trace("liastar-ext-smt") << "(assert " << std::endl
                             << "  (distinct" << std::endl
                             << "    ";
    Trace("liastar-ext-smt") << n << std::endl << "    ";
    Trace("liastar-ext-smt") << noItes << std::endl
                             << "  )" << std::endl
                             << ")" << std::endl;
    Trace("liastar-ext-smt") << "(check-sat)" << std::endl;
    // nnf
    Trace("liastar-ext-smt") << "(pop 1)" << std::endl;
    Trace("liastar-ext-smt") << "(push 1)" << std::endl;
    Trace("liastar-ext-smt") << "(echo \"nnf\")" << std::endl;
    Trace("liastar-ext-smt") << "(assert " << std::endl
                             << "  (distinct" << std::endl
                             << "    ";
    Trace("liastar-ext-smt") << noItes << std::endl << "    ";
    Trace("liastar-ext-smt") << nnf << std::endl
                             << "  )" << std::endl
                             << ")" << std::endl;
    Trace("liastar-ext-smt") << "(check-sat)" << std::endl;
    Trace("liastar-ext-smt") << "(pop 1)" << std::endl;
  }
  // distributes conjunctions over disjunctions  
  Node dnf = distribute(nnf, e);
  Trace("liastar-ext-debug") << "dnf: " << dnf << std::endl;
  // dnf = recursiveFlatten(e->getNodeManager(), dnf);
  if (TraceIsOn("liastar-ext-smt"))
  {    
    Trace("liastar-ext-smt") << "(push 1)" << std::endl;
    Trace("liastar-ext-smt") << "(echo \"dnf\")" << std::endl;
    Trace("liastar-ext-smt") << "(assert " << std::endl
                             << "  (distinct" << std::endl
                             << "    ";
    Trace("liastar-ext-smt") << nnf << std::endl << "    ";
    Trace("liastar-ext-smt") << dnf << std::endl
                             << "  )" << std::endl
                             << ")" << std::endl;
    Trace("liastar-ext-smt") << "(check-sat)" << std::endl;
    Trace("liastar-ext-smt") << "(pop 1)" << std::endl;
  }
  return dnf;
}

Node LiaStarUtils::recursiveFlatten(NodeManager* nm, Node n)
{
  Trace("liastar-ext-dnf") << "recursiveFlatten::n: " << n << std::endl;
  if (n.getNumChildren() == 0)
  {
    return n;
  }
  Node flat = expr::algorithm::flatten(nm, n);
  std::vector<Node> children;
  for (const auto& child : flat)
  {
    children.push_back(expr::algorithm::flatten(nm, child));
  }
  return nm->mkNode(flat.getKind(), children);
}

Node LiaStarUtils::distribute(Node n, Env* e)
{
  Assert(n.getType().isBoolean())
      << "Expected " << n << " to be boolean" << std::endl;
  Trace("liastar-ext-dnf") << "distribute::n: " << n << std::endl;
  NodeManager* nm = e->getNodeManager();
  Node falseConst = nm->mkConst<bool>(false);
  Node trueConst = nm->mkConst<bool>(true);

  Kind k = n.getKind();
  switch (k)
  {
    case Kind::BOUND_VARIABLE:
    case Kind::CONST_BOOLEAN:
    case Kind::LT:
    case Kind::GT:
    case Kind::LEQ:
    case Kind::GEQ:
    case Kind::EQUAL:
    {
      return n;
    }
    case Kind::AND:
    {
      std::vector<Node> conjunctions;
      for (Node child : n)
      {
        Node childDnf = distribute(child, e);
        childDnf = expr::algorithm::flatten(nm, childDnf);
        conjunctions.push_back(childDnf);
      }

      if (conjunctions.size() == 1)
      {
        return conjunctions[0];
      }
      // basically we compute the cartesian product
      std::vector<std::vector<Node>> disjunctions;
      disjunctions.push_back({});
      // {a, b}
      // {c}
      // {d, e}
      // ****
      // disjunctions: {}
      // disjunctions: {a}, {b}
      // disjunctions: {a, c}, {b, c}
      // disjunctions: {a,c, d},{b, d, d},{a, c, e},{b, c, e}
      for (const Node& conjunct : conjunctions)
      {
        Kind conjunctKind = conjunct.getKind();
        if (conjunctKind == Kind::OR)
        {
          std::vector<std::vector<Node>> tmp;
          for (const Node& disjunct : conjunct)
          {
            auto copy = disjunctions;
            for (std::vector<Node>& v : copy)
            {
              v.push_back(disjunct);
              tmp.push_back(v);
            }
          }
          disjunctions = std::move(tmp);
        }
        else
        {
          for (size_t i = 0; i < disjunctions.size(); i++)
          {
            disjunctions[i].push_back(conjunct);
          }
        }
      }
      std::vector<Node> final_disjuncts;
      for (std::vector<Node>& v : disjunctions)
      {
        if (v.size() == 1)
        {
          final_disjuncts.push_back(v[0]);
        }
        else
        {
          final_disjuncts.push_back(nm->mkNode(Kind::AND, v));
        }
      }
      if (final_disjuncts.size() == 1)
      {
        return final_disjuncts[0];
      }
      return nm->mkNode(Kind::OR, final_disjuncts);
    }
    case Kind::OR:
    {
      std::vector<Node> disjuncts;

      for (size_t i = 0; i < n.getNumChildren(); i++)
      {
        Node childDnf = distribute(n[i], e);
        childDnf = expr::algorithm::flatten(nm, childDnf);
        disjuncts.push_back(childDnf);
      }

      return nm->mkNode(Kind::OR, disjuncts);
    }

    default:
    {
      break;
    }
  }
  InternalError() << "Unexpected kind. Node " << n
                  << " has kind: " << n.getKind() << std::endl;
}

Node LiaStarUtils::removeItes(Node n, Env* e)
{
  NodeManager* nm = e->getNodeManager();
  Node falseConst = nm->mkConst<bool>(false);
  Node trueConst = nm->mkConst<bool>(true);
  Kind k = n.getKind();
  switch (k)
  {
    case Kind::BOUND_VARIABLE:
    case Kind::CONST_BOOLEAN: return n;
    case Kind::LT:
    case Kind::GT:
    case Kind::LEQ:
    case Kind::GEQ:
    case Kind::EQUAL:
    {
      std::vector<std::pair<Node, Node>> left = removeIntegerItes(n[0], e);
      std::vector<std::pair<Node, Node>> right = removeIntegerItes(n[1], e);
      if (left.size() == 1 && right.size() == 1)
      {
        return n;
      }

      // combine the conditions of left and right
      std::vector<Node> disjunctions;
      for (const auto& l : left)
      {
        for (const auto& r : right)
        {
          Node result = nm->mkNode(k, l.second, r.second);
          Node combined = result;
          if (r.first != trueConst)
          {
            combined = combined.andNode(r.first);
          }
          else if (l.first != trueConst)
          {
            combined = combined.andNode(l.first);
          }
          disjunctions.push_back(combined);
        }
      }
      return nm->mkNode(Kind::OR, disjunctions);
    }
    case Kind::ITE:
    {
      Node l = removeItes(n[0].andNode(n[1]), e);
      Node r = removeItes(n[0].notNode().andNode(n[2]), e);
      return l.orNode(r);
    }
    case Kind::AND:
    {
      std::vector<Node> conjuncts;
      for (Node child : n)
      {
        conjuncts.push_back(removeItes(child, e));
      }
      return nm->mkNode(Kind::AND, conjuncts);
    }
    case Kind::OR:
    {
      std::vector<Node> disjuncts;
      for (Node child : n)
      {
        disjuncts.push_back(removeItes(child, e));
      }
      return nm->mkNode(Kind::OR, disjuncts);
    }
    case Kind::NOT:
    {
      return removeItes(n[0], e).notNode();
    }
    default:
    {
      break;
    }
  }
  InternalError() << "Unexpected kind. Node " << n
                  << " has kind: " << n.getKind() << std::endl;
}

Node LiaStarUtils::removeNot(Node n, Env* e)
{
  NodeManager* nm = e->getNodeManager();
  // eliminate negation nodes of the form (not (or ...)), (not (and ...))
  Node nnf = booleans::TheoryBoolRewriter::computeNnfNorm(nm, n);
  Kind k = nnf.getKind();
  switch (k)
  {
    case Kind::BOUND_VARIABLE:
    case Kind::CONST_BOOLEAN:
    case Kind::LT:
    case Kind::GT:
    case Kind::LEQ:
    case Kind::GEQ:
    case Kind::EQUAL: return nnf;
    case Kind::AND:
    {
      std::vector<Node> conjuncts;
      for (Node child : nnf)
      {
        conjuncts.push_back(removeNot(child, e));
      }
      return nm->mkNode(Kind::AND, conjuncts);
    }
    case Kind::OR:
    {
      std::vector<Node> disjuncts;
      for (Node child : nnf)
      {
        disjuncts.push_back(removeNot(child, e));
      }
      return nm->mkNode(Kind::OR, disjuncts);
    }
    case Kind::NOT:
    {
      Kind kind = nnf[0].getKind();
      switch (kind)
      {
        case Kind::LT:
        {
          //(not (< a b)) is rewritten as (>= a b)
          return nm->mkNode(Kind::GEQ, nnf[0][0], nnf[0][1]);
        }
        case Kind::GT:
        {
          //(not (> a b)) is rewritten as (<= a b)
          return nm->mkNode(Kind::LEQ, nnf[0][0], nnf[0][1]);
        }
        case Kind::LEQ:
        {
          //(not (<= a b)) is rewritten as (> a b)
          return nm->mkNode(Kind::GT, nnf[0][0], nnf[0][1]);
        }
        case Kind::GEQ:
        {
          //(not (>= a b)) is rewritten as (< a b)
          return nm->mkNode(Kind::LT, nnf[0][0], nnf[0][1]);
        }
        case Kind::EQUAL:
        {
          // (not (= a b)) is rewritten as (or (> a b) (< a b))
          Node a = nnf[0][0];
          Node b = nnf[0][1];
          Node gt = nm->mkNode(Kind::GT, a, b);
          Node lt = nm->mkNode(Kind::LT, a, b);
          return gt.orNode(lt);
        }
        default:
          InternalError() << "Unexpected negated kind. Node " << n
                          << " has kind: " << n.getKind() << std::endl;
      }
      break;
    }
    default:
    {
      break;
    }
  }
  InternalError() << "Unexpected kind. Node " << n
                  << " has kind: " << n.getKind() << std::endl;
}

std::vector<std::pair<Node, Node>> LiaStarUtils::removeIntegerItes(Node n,
                                                                   Env* e)
{
  Assert(n.getType().isInteger());
  // (+
  //    (ite c1 a b)
  //    (ite c2 c d))
  // should return 4 pairs:
  // <(and c1 c2)           ,(+ a c)>
  // <(and c1 (not c2)      ,(+ a d)>
  // <(and (not c1) c2)     ,(+ b c)>
  // <(and (not c1) (not c2),(+ b d)>
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
      std::vector<std::pair<Node, Node>> left = removeIntegerItes(n[0], e);
      std::vector<std::pair<Node, Node>> right = removeIntegerItes(n[1], e);
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
      Node condition = removeItes(n[0], e);
      std::vector<std::pair<Node, Node>> thenPart = removeIntegerItes(n[1], e);
      for (const auto& pair : thenPart)
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

      // todo: restore this line Node notCondition =
      // rw->rewrite(condition.notNode());
      Node notCondition = condition.notNode();
      std::vector<std::pair<Node, Node>> elsePart = removeIntegerItes(n[2], e);
      for (const auto& pair : elsePart)
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
      break;
    }
  }
  InternalError() << "Unexpected kind. Node " << n
                  << " has kind: " << n.getKind() << std::endl;
}

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_NORMALIZ */