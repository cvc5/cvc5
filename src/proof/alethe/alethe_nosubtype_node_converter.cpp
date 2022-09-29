/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of Alethe node conversion to remove subtyping
 */

#include "proof/alethe/alethe_nosubtype_node_converter.h"

#include "expr/node_algorithm.h"
#include "theory/theory.h"

namespace cvc5::internal {
namespace proof {

Node AletheNoSubtypeNodeConverter::postConvert(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  // corce function applications
  if (n.getKind() == kind::APPLY_UF)
  {
    Node op = n.getOperator();
    TypeNode tn = op.getType();
    std::vector<TypeNode> argTypes = tn.getArgTypes();
    // if any of the argument types is real, in case the argument of that
    // position is an integer constant we must turn it into a real constant
    // look at all args, if any is an integer constant, transform it
    bool childChanged = false;
    std::vector<Node> children{op};
    for (size_t i = 0, size = n.getNumChildren(); i < size; ++i)
    {
      if (!argTypes[i].isRealOrInt() || argTypes[i].isInteger()
          || !n[i].isConst() || !n[i].getType().isInteger())
      {
        children.push_back(n[i]);
        continue;
      }
      Trace("alethe-proof-subtyping")
          << "\t\t..fun app arg " << i << " is integer term " << n[i]
          << " in real position.\n";
      if (!n[i].isConst())
      {
        // there are two cases here: either this is a term that contains
        // somewhere an uninterpreted constant or not. If it does not, than
        // this is easily salvageable. Otherwise it's not.
        if (expr::hasSubtermKinds({kind::APPLY_UF, kind::SKOLEM}, n[i]))
        {
          // Unreachable() << "AletheBackend: Can't handle subtyping case of "
          //                  "non-value integers.\n";
          Trace("alethe-proof-subtyping")
              << "\t\t..traverse and convert consts in term, then apply a "
                 "to_real over it\n";
          childChanged = true;
          children.push_back(
              nm->mkNode(kind::TO_REAL, traverseAndConvertAllConsts(n[i])));
          Trace("alethe-proof-subtyping")
              << "\t\t..converted " << n[i] << " into " << children.back()
              << "\n";
        }
        Trace("alethe-proof-subtyping")
            << "\t\t..traverse and convert term with only consts\n";
        childChanged = true;
        children.push_back(traverseAndConvertAllConsts(n[i]));
        Trace("alethe-proof-subtyping") << "\t\t..converted " << n[i]
                                        << " into " << children.back() << "\n";
        continue;
      }
      childChanged = true;
      children.push_back(nm->mkNode(kind::TO_REAL, n[i]));
    }
    if (childChanged)
    {
      return nm->mkNode(kind::APPLY_UF, children);
    }
    return n;
  }
  // Ignore interpreted terms that are not applications of arithmetic operators
  // (or equalities between arithmetic terms) which may have a real and an
  // integer argument
  if (n.getNumChildren() < 2
      || theory::Theory::theoryOf(n) != theory::TheoryId::THEORY_ARITH)
  {
    if (n.getNumChildren() > 1)
    {
      Trace("alethe-proof-subtyping2") << "\tIgnoring " << n << " with theory "
                                       << theory::Theory::theoryOf(n) << "\n";
    }
    return n;
  }
  Trace("alethe-proof-subtyping2")
      << "\tCheck " << n << " of kind " << n.getKind() << "\n";
  // coerce equalities where one of the terms is real and the other integer.
  // This handles for example the case instantiation
  bool childChanged = false;
  std::vector<Node> children{n.begin(), n.end()};
  size_t i, size = n.getNumChildren();
  size_t hasReal = size;
  for (i = 0; i < size; ++i)
  {
    if (n[i].getType().isReal() && !n[i].getType().isInteger())
    {
      hasReal = i;
      break;
    }
  }
  if (hasReal < size)
  {
    for (i = 0; i < size; ++i)
    {
      if (n[i].getType().isInteger())
      {
        Trace("alethe-proof-subtyping")
            << "\t\t..arg " << i << ", arith term " << n[i] << " (kind "
            << n[i].getKind() << "), is integer but should be real, from arg "
            << hasReal << " " << n[hasReal] << " (kind " << n[hasReal].getKind()
            << ")\n";
        if (!n[i].isConst())
        {
          // there are two cases here: either this is a term that contains
          // somewhere an uninterpreted constant or not. If it does not, than
          // this is salvageable. Otherwise it's not.
          if (expr::hasSubtermKinds({kind::APPLY_UF, kind::SKOLEM}, n[i]))
          {
            Unreachable() << "AletheBackend: Can't handle subtyping case of "
                             "non-value integers.\n";
          }
          Trace("alethe-proof-subtyping")
              << "\t\t..traverse and convert term with only consts\n";
          childChanged = true;
          children[i] = traverseAndConvertAllConsts(n[i]);
          Trace("alethe-proof-subtyping")
              << "\t\t..converted " << n[i] << " into " << children[i] << "\n";
          continue;
        }
        childChanged = true;
        children[i] = nm->mkNode(kind::TO_REAL, n[i]);
        break;
      }
    }
    if (childChanged)
    {
      return nm->mkNode(n.getKind(), children);
    }
  }
  return n;
}

Node AletheNoSubtypeNodeConverter::traverseAndConvertAllConsts(Node n)
{
  std::unordered_map<Node, Node> visited;
  std::unordered_map<Node, Node>::iterator it;
  std::vector<Node> visit;
  Node cur;
  visit.push_back(n);
  NodeManager* nm = NodeManager::currentNM();
  do
  {
    cur = visit.back();
    visit.pop_back();
    Trace("alethe-proof-subtyping-convert")
        << "traverseAndConvertAllConsts: convert " << cur << "\n";
    if (cur.getMetaKind() == kind::metakind::PARAMETERIZED
        || cur.getKind() == kind::TO_REAL)
    {
      visited[cur] = cur;
      Trace("alethe-proof-subtyping-convert")
          << "traverseAndConvertAllConsts: ignore " << cur << " with kind "
          << cur.getKind() << " and metakind " << cur.getMetaKind() << "\n";
      continue;
    }
    it = visited.find(cur);
    if (it == visited.end())
    {
      if (cur.isConst() && cur.getType().isInteger())
      {
        Trace("alethe-proof-subtyping-convert") << "..cast int conts to real\n";
        visited[cur] = nm->mkNode(kind::TO_REAL, cur);
        continue;
      }
      if (cur.getNumChildren() > 0)
      {
        visited[cur] = Node::null();
        visit.push_back(cur);
        visit.insert(visit.end(), cur.begin(), cur.end());
        Trace("alethe-proof-subtyping-convert") << push;
      }
      else
      {
        visited[cur] = cur;
      }
    }
    else if (it->second.isNull())
    {
      Trace("alethe-proof-subtyping-convert") << pop;
      bool childChanged = false;
      std::vector<Node> children;
      for (const Node& child : cur)
      {
        AlwaysAssert(visited.find(child) != visited.end());
        childChanged |= child != visited[child];
        children.push_back(visited[child]);
      }
      visited[cur] = !childChanged ? cur : nm->mkNode(cur.getKind(), children);
      if (TraceIsOn("alethe-proof-subtyping-convert") && childChanged)
      {
        Trace("alethe-proof-subtyping-convert")
            << "..rebuilt " << cur << " into " << visited[cur] << "\n";
      }
    }
  } while (!visit.empty());
  return visited[n];
}

}  // namespace proof
}  // namespace cvc5::internal
